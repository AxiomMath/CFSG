module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma24
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.Proving.Basic
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeDecomp
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  (commutator_le_of_normalizer conj_mem_commutator le_sup_centralizer_commutator)

@[expose] def IsLThreeEpsOrON (X : Type*) [Group X] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K % 3 ≠ 0 ∧
      Nonempty (X ≃* (↥(StatedSL 3 K) ⧸ Subgroup.center ↥(StatedSL 3 K)))) ∨
  (∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ), Nat.card K = q ^ 2 ∧ q % 3 ≠ 0 ∧ q ≠ 8 ∧
      Nonempty (X ≃* (↥(StatedSU 3 q K) ⧸ Subgroup.center ↥(StatedSU 3 q K)))) ∨
  Nonempty (X ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group)

@[expose] def Input23_26 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsKGroup Y →
    ∀ 𝒮 : Set (Subgroup Y), (∀ J ∈ 𝒮, IsComponentOf J ⊤) →
      (∀ J ∈ 𝒮, IsLThreeEpsOrON (↥J ⧸ Subgroup.center ↥J)) →
      ∀ E : Subgroup Y, IsElemAbelian 3 E → Nat.card E = 27 →
        E ≤ Subgroup.normalizer ((⨆ J ∈ 𝒮, J : Subgroup Y) : Set Y) →
          (⨆ J ∈ 𝒮, J : Subgroup Y) =
            ⨆ e ∈ E, ⨆ (_ : e ≠ 1),
              GLAPLayer 3 ((⨆ J ∈ 𝒮, J : Subgroup Y) ⊓ Subgroup.centralizer ({e} : Set Y))

@[expose] def Input18_2One : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsKGroup Y → ∀ p : ℕ, p.Prime →
    ∀ E : Subgroup Y, IsPGroup p E →
      GLAPLayer p (GLAPLayer p (⊤ : Subgroup Y) ⊓ Subgroup.centralizer (E : Set Y)) =
        GLAPLayer p (Subgroup.centralizer (E : Set Y))

@[expose] def Input14_5Second : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsKGroup Y → GLAPPrimeCore 3 Y = ⊥ →
    ∀ Q : Subgroup Y, Q ≠ ⊥ → IsPGroup 3 Q →
      ⁅GLAPLayer 3 (Subgroup.normalizer (Q : Set Y)),
        GLAPPrimeCoreOf 3 (Subgroup.normalizer (Q : Set Y))⁆ = ⊥

section Generic

variable {G : Type*} [Group G]

open scoped commutatorElement

theorem l28b_T1_conj_comm {Y K : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (Y : Set G))
    (hgK : ∀ k ∈ K, g * k = k * g) {n : G} (hn : n ∈ ⁅Y, K⁆) : g * n * g⁻¹ ∈ ⁅Y, K⁆ := by
  rw [Subgroup.commutator_def] at hn ⊢
  refine Subgroup.closure_induction (p := fun n _ => g * n * g⁻¹ ∈
    Subgroup.closure {x | ∃ g₁ ∈ Y, ∃ g₂ ∈ K, ⁅g₁, g₂⁆ = x}) ?_ ?_ ?_ ?_ hn
  · rintro _ ⟨y, hy, k, hk, rfl⟩
    have h1 : g * y * g⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 hg y).1 hy
    have hk' : g * k * g⁻¹ = k := by rw [hgK k hk]; group
    have e : g * ⁅y, k⁆ * g⁻¹ = ⁅g * y * g⁻¹, k⁆ := by
      calc g * ⁅y, k⁆ * g⁻¹ = ⁅g * y * g⁻¹, g * k * g⁻¹⁆ := by
            simp only [commutatorElement_def]; group
        _ = _ := by rw [hk']
    rw [e]
    exact Subgroup.subset_closure ⟨_, h1, _, hk, rfl⟩
  · simp
  · intro x y _ _ hx hy
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem l28b_T1_conj_normal {Y K : Subgroup G} (_hKY : K ≤ Subgroup.normalizer (Y : Set G))
    {w : G} (hw : w ∈ Y) {n : G} (hn : n ∈ ⁅Y, K⁆) : w * n * w⁻¹ ∈ ⁅Y, K⁆ := by
  rw [Subgroup.commutator_def] at hn
  refine Subgroup.closure_induction (p := fun n _ => w * n * w⁻¹ ∈ ⁅Y, K⁆) ?_ ?_ ?_ ?_ hn
  · rintro _ ⟨y, hy, k, hk, rfl⟩
    have e : w * ⁅y, k⁆ * w⁻¹ = ⁅w * y, k⁆ * ⁅w, k⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (Y.mul_mem hw hy) hk)
      (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hw hk))
  · simp
  · intro x y _ _ hx hy
    have : w * (x * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    have : w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem l28b_T1_mem_sup {C N : Subgroup G} (hCN : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    {x : G} (hx : x ∈ C ⊔ N) : ∃ c ∈ C, ∃ n ∈ N, x = c * n := by
  let S : Subgroup G :=
    { carrier := {x | ∃ c ∈ C, ∃ n ∈ N, x = c * n}
      one_mem' := ⟨1, C.one_mem, 1, N.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨c, hc, n, hn, rfl⟩ ⟨c', hc', n', hn', rfl⟩
        refine ⟨c * c', C.mul_mem hc hc', (c'⁻¹ * n * c'⁻¹⁻¹) * n',
          N.mul_mem ?_ hn', by group⟩
        exact hCN _ (C.inv_mem hc') _ hn
      inv_mem' := by
        rintro _ ⟨c, hc, n, hn, rfl⟩
        refine ⟨c⁻¹, C.inv_mem hc, c * n⁻¹ * c⁻¹, hCN _ hc _ (N.inv_mem hn), by group⟩ }
  have : C ⊔ N ≤ S := sup_le (fun c hc => ⟨c, hc, 1, N.one_mem, by simp⟩)
    (fun n hn => ⟨1, C.one_mem, n, hn, by simp⟩)
  exact this hx

theorem l28b_T1_comm_mul {c n β : G} :
    ⁅c * n, β⁆ = c * ⁅n, β⁆ * c⁻¹ * ⁅c, β⁆ := by
  simp only [commutatorElement_def]; group

theorem l28b_commutator_decomp [Finite G] {p : ℕ} [Fact p.Prime] {W B : Subgroup G} {b : G}
    (hB : IsElemAbelian p B) (hBW : B ≤ Subgroup.normalizer (W : Set G))
    (hW : Nat.Coprime p (Nat.card W)) (hb : b ∈ B) :
    ⁅W, B⁆ ≤ ⁅⁅W, B⁆ ⊓ Subgroup.centralizer ({b} : Set G), B⁆ ⊔
      ⁅⁅W, B⁆, Subgroup.zpowers b⁆ := by
  have hpB : IsPGroup p B := fun x =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hB.2 x x.2)⟩
  have hcomm : ∀ β ∈ B, β * b = b * β := fun β hβ => by
    have := hB.1.is_comm.comm ⟨β, hβ⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val this
  set U : Subgroup G := ⁅W, B⁆ with hU
  have hUW : U ≤ W := commutator_le_of_normalizer hBW
  have hBU : B ≤ Subgroup.normalizer (U : Set G) := by
    intro β hβ
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => conj_mem_commutator hBW hβ hh, fun hh => ?_⟩
    have := conj_mem_commutator hBW (B.inv_mem hβ) hh
    simpa [mul_assoc] using this
  have hWU : ∀ w ∈ W, w ∈ Subgroup.normalizer (U : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => l28b_T1_conj_normal hBW hw hh, fun hh => ?_⟩
    have := l28b_T1_conj_normal hBW (W.inv_mem hw) hh
    simpa [mul_assoc] using this
  have hzB : Subgroup.zpowers b ≤ B := by
    rw [Subgroup.zpowers_le]; exact hb
  have hzU : Subgroup.zpowers b ≤ Subgroup.normalizer (U : Set G) := hzB.trans hBU
  have hpz : IsPGroup p (Subgroup.zpowers b) := fun x =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hB.2 x (hzB x.2))⟩
  have hUcop : Nat.Coprime p (Nat.card U) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hUW) hW
  have h1 : W ≤ (W ⊓ Subgroup.centralizer (B : Set G)) ⊔ U :=
    le_sup_centralizer_commutator hpB hBW hW
  have hstep2 : U ≤ ⁅U, B⁆ := by
    rw [hU, Subgroup.commutator_le]
    intro w hw β hβ
    obtain ⟨c, hc, n, hn, rfl⟩ := l28b_T1_mem_sup (C := W ⊓ Subgroup.centralizer (B : Set G))
      (N := U) (fun c hc n hn => by
        have : c ∈ Subgroup.normalizer (U : Set G) := hWU c hc.1
        exact (Subgroup.mem_normalizer_iff.1 this n).1 hn) (h1 hw)
    have hcB : ∀ k ∈ B, c * k = k * c := fun k hk =>
      (Subgroup.mem_centralizer_iff.1 hc.2 k hk).symm
    have hcβ : ⁅c, β⁆ = 1 := by
      simp only [commutatorElement_def]
      rw [hcB β hβ]; group
    rw [l28b_T1_comm_mul, hcβ, mul_one]
    exact l28b_T1_conj_comm (hWU c hc.1) hcB (Subgroup.commutator_mem_commutator hn hβ)
  have h3 : U ≤ (U ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G)) ⊔
      ⁅U, Subgroup.zpowers b⁆ :=
    le_sup_centralizer_commutator hpz hzU hUcop
  have hstep3 : ⁅U, B⁆ ≤ ⁅U ⊓ Subgroup.centralizer ({b} : Set G), B⁆ ⊔ ⁅U, Subgroup.zpowers b⁆ := by
    rw [Subgroup.commutator_le]
    intro u hu β hβ
    obtain ⟨c, hc, z, hz, rfl⟩ := l28b_T1_mem_sup
      (C := U ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G))
      (N := ⁅U, Subgroup.zpowers b⁆) (fun c hc n hn =>
        l28b_T1_conj_normal hzU hc.1 hn) (h3 hu)
    have hcb : c ∈ U ⊓ Subgroup.centralizer ({b} : Set G) :=
      ⟨hc.1, Subgroup.mem_centralizer_iff.2 (fun h hh => by
        rw [Set.mem_singleton_iff] at hh; subst hh
        exact Subgroup.mem_centralizer_iff.1 hc.2 h (Subgroup.mem_zpowers h))⟩
    have hzU' : z ∈ U :=
      commutator_le_of_normalizer hzU hz
    have hβz : ∀ k ∈ Subgroup.zpowers b, β * k = k * β := by
      intro k hk
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      exact ((Commute.zpow_right (show Commute β b from hcomm β hβ) m)).eq
    have h1 : β * z⁻¹ * β⁻¹ ∈ ⁅U, Subgroup.zpowers b⁆ :=
      l28b_T1_conj_comm (hBU hβ) hβz (Subgroup.inv_mem _ hz)
    have h2 : ⁅z, β⁆ ∈ ⁅U, Subgroup.zpowers b⁆ := by
      have : ⁅z, β⁆ = z * (β * z⁻¹ * β⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]; exact Subgroup.mul_mem _ hz h1
    have h3 : c * ⁅z, β⁆ * c⁻¹ ∈ ⁅U, Subgroup.zpowers b⁆ := l28b_T1_conj_normal hzU hc.1 h2
    rw [l28b_T1_comm_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h3)
      (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hcb hβ))
  exact hstep2.trans (hstep3)

theorem l28b_le_oPrimePOf_of_pow_mem [Finite G] {p : ℕ} (hp : p.Prime) {H S N₀ : Subgroup G}
    (hSH : S ≤ H) (hS : (S.subgroupOf H).Normal) (hNH : N₀ ≤ H) (hN : (N₀.subgroupOf H).Normal)
    (hcop : Nat.Coprime p (Nat.card N₀)) (hpow : ∀ s ∈ S, ∃ n : ℕ, s ^ (p ^ n) ∈ N₀) :
    S ≤ oPrimePOf p H := by
  have : Fact p.Prime := ⟨hp⟩
  have hcop' : Nat.Coprime p (Nat.card (N₀.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    exact hcop
  have hN0 : N₀.subgroupOf H ≤ GLAPPrimeCore p ↥H := le_sSup ⟨hN, hcop'⟩
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥H) with hπ
  set Sb : Subgroup (↥H ⧸ GLAPPrimeCore p ↥H) := (S.subgroupOf H).map π with hSb
  have hSbn : Sb.Normal := hS.map π (QuotientGroup.mk'_surjective _)
  have hSbp : IsPGroup p Sb := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨_, ⟨s, hs, rfl⟩⟩
    obtain ⟨n, hn⟩ := hpow (s : G) (Subgroup.mem_subgroupOf.1 hs)
    have h1 : π s ^ (p ^ n) = 1 := by
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff _).2
      apply hN0
      exact Subgroup.mem_subgroupOf.2 (by simpa using hn)
    have h2 : orderOf (⟨π s, ⟨s, hs, rfl⟩⟩ : Sb) ∣ p ^ n := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 h2
    exact ⟨k, hk⟩
  have hle : Sb ≤ CFSG.pCore p (↥H ⧸ GLAPPrimeCore p ↥H) :=
    le_sSup ⟨hSbn, hSbp⟩
  intro s hs
  refine ⟨⟨s, hSH hs⟩, ?_, rfl⟩
  exact hle ⟨⟨s, hSH hs⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩


theorem l28b_pCore_map_le (p : ℕ) {Q : Type*} [Group Q] (σ : Q ≃* Q) :
    (CFSG.pCore p Q).map σ.toMonoidHom ≤ CFSG.pCore p Q := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_sSup ⟨hK.1.map σ.toMonoidHom σ.surjective, ?_⟩
  exact hK.2.map σ.toMonoidHom

theorem l28b_oPrimePOf_le_of_normal [Finite G] {p : ℕ} (hp : p.Prime) {C N : Subgroup G}
    (hCN : C ≤ N) (hn : (C.subgroupOf N).Normal) : oPrimePOf p C ≤ oPrimePOf p N := by
  have hNC : N ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).1 hn
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥C) with hπ
  have hmemN0 : ∀ s : G, s ∈ GLAPPrimeCoreOf p C ↔ ∃ h : s ∈ C, π ⟨s, h⟩ = 1 := by
    intro s
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.2, (QuotientGroup.eq_one_iff _).2 ht⟩
    · rintro ⟨h, h1⟩
      exact ⟨⟨s, h⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  have hmemS : ∀ s : G, s ∈ oPrimePOf p C ↔
      ∃ h : s ∈ C, π ⟨s, h⟩ ∈ CFSG.pCore p (↥C ⧸ GLAPPrimeCore p ↥C) := by
    intro s
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.2, ht⟩
    · rintro ⟨h, h1⟩
      exact ⟨⟨s, h⟩, h1, rfl⟩
  have hconjC : ∀ n ∈ N, ∀ s ∈ C, n * s * n⁻¹ ∈ C := fun n hn s hs =>
    (Subgroup.mem_normalizer_iff.1 (hNC hn) s).1 hs
  have hact : ∀ n : ↥N, ∀ (s : G) (h : s ∈ C),
      π ⟨(n : G) * s * (n : G)⁻¹, hconjC n n.2 s h⟩ =
        barAut p C ⟨(n : G), hNC n.2⟩ (π ⟨s, h⟩) := by
    intro n s h
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, barAut_mk]
    rfl
  have hS : (oPrimePOf p C).subgroupOf N |>.Normal := by
    refine ⟨fun s hs n => ?_⟩
    have hs' : (s : G) ∈ oPrimePOf p C := hs
    obtain ⟨h, hπs⟩ := (hmemS _).1 hs'
    show (n : G) * (s : G) * (n : G)⁻¹ ∈ oPrimePOf p C
    refine (hmemS _).2 ⟨hconjC n n.2 s h, ?_⟩
    rw [hact n s h]
    have := l28b_pCore_map_le p (barAut p C ⟨(n : G), hNC n.2⟩) 
    exact this ⟨_, hπs, rfl⟩
  have hN0 : (GLAPPrimeCoreOf p C).subgroupOf N |>.Normal := by
    refine ⟨fun s hs n => ?_⟩
    have hs' : (s : G) ∈ GLAPPrimeCoreOf p C := hs
    obtain ⟨h, hπs⟩ := (hmemN0 _).1 hs'
    show (n : G) * (s : G) * (n : G)⁻¹ ∈ GLAPPrimeCoreOf p C
    refine (hmemN0 _).2 ⟨hconjC n n.2 s h, ?_⟩
    rw [hact n s h, hπs, map_one]
  have hSN : oPrimePOf p C ≤ N := by
    intro s hs
    obtain ⟨h, -⟩ := (hmemS _).1 hs
    exact hCN h
  have hN0N : GLAPPrimeCoreOf p C ≤ N := by
    intro s hs
    obtain ⟨h, -⟩ := (hmemN0 _).1 hs
    exact hCN h
  refine l28b_le_oPrimePOf_of_pow_mem hp hSN hS hN0N hN0 ?_ ?_
  · exact (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp C)
  · intro s hs
    obtain ⟨h, hπs⟩ := (hmemS _).1 hs
    have hpg : IsPGroup p (CFSG.pCore p (↥C ⧸ GLAPPrimeCore p ↥C)) := CFSG.pCore_isPGroup
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hpg ⟨_, hπs⟩
    refine ⟨k, (hmemN0 _).2 ⟨?_, ?_⟩⟩
    · exact C.pow_mem h _
    · have h1 : orderOf (π ⟨s, h⟩) = p ^ k := by
        have := Subgroup.orderOf_coe (⟨_, hπs⟩ : CFSG.pCore p (↥C ⧸ GLAPPrimeCore p ↥C))
        rw [hk] at this
        exact this
      have h2 : π ⟨s, h⟩ ^ (p ^ k) = 1 := by rw [← h1]; exact pow_orderOf_eq_one _
      rw [← h2, ← map_pow]
      rfl

theorem l28b_T3_component_of_normal [Finite G] {p : ℕ} (hp : p.Prime) {N H J : Subgroup G}
    (hNH : N ≤ H) (hn : (N.subgroupOf H).Normal) (hJ : GLAPComponent p N J) :
    GLAPComponent p H J := by
  obtain ⟨hJN, hsn, hcomp, hmin⟩ := hJ
  have hNsn : IsSubnormal N H := IsSubnormal.step hNH hn (IsSubnormal.refl H)
  have hsnH : IsSubnormal J H := isSubnormal_trans' hsn hNsn
  have hJH : J ≤ H := hJN.trans hNH
  refine ⟨hJH, hsnH, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := H) p hsnH
    rwa [barX_self] at this
  · have e : ↥(barX p N J) ≃* ↥(barX p H J) :=
      (quotEquivBarX hp hJN hsn).symm.trans (quotEquivBarX hp hJH hsnH)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hcomp.2.2
  · intro J' hlt hJ'sn heq
    have hJ'J : J' ≤ J := hlt.le
    have hJ'N : IsSubnormal J' N := isSubnormal_of_le_of_le hJ'sn (hJ'J.trans hJN) hNH
    have hcore : J ⊓ GLAPPrimeCoreOf p H ≤ GLAPPrimeCoreOf p N := by
      rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hNsn]
      exact inf_le_inf_right _ hJN
    refine hmin J' hlt hJ'N ?_
    show barX p N J' = barX p N J
    refine le_antisymm (barX_mono p hJ'J) ?_
    refine barX_le_of_forall (hJ'J.trans hJN) (fun k hk => ?_)
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := H) (le_of_eq heq.symm) hk (hJH hk)
    exact ⟨j, hj, hcore ⟨J.mul_mem (J.inv_mem (hJ'J hj)) hk, hjk⟩⟩

theorem l28b_glaPLayer_le_of_normal [Finite G] {p : ℕ} (hp : p.Prime) {N H : Subgroup G}
    (hNH : N ≤ H) (hn : (N.subgroupOf H).Normal) : GLAPLayer p N ≤ GLAPLayer p H := by
  refine sSup_le fun J hJ => le_sSup (l28b_T3_component_of_normal hp hNH hn hJ)

theorem l28b_commutator_glaPLayer_le [Finite G] {p : ℕ} (hp : p.Prime) (H : Subgroup G) :
    ⁅GLAPLayer p H, oPrimePOf p H⁆ ≤ GLAPPrimeCoreOf p H := by
  classical
  have := Fact.mk hp
  set Q := ↥H ⧸ GLAPPrimeCore p ↥H with hQ
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥H) with hπ
  set T := oPrimePOf p H with hT
  have hTH : T ≤ H := Subgroup.map_subtype_le _
  have hTb : barX p H T ≤ CFSG.pCore p Q := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨x, hx, hxt⟩ := (Subgroup.mem_subgroupOf.1 ht : (t : G) ∈ T)
    have : x = t := Subtype.ext hxt
    subst this
    exact hx
  have hcomm : ∀ L : Subgroup G, GLAPComponent p H L →
      barX p H L ≤ Subgroup.centralizer (barX p H T : Set Q) := by
    intro L hL
    have hLc : IsComponentOf (barX p H L) ⊤ := hL.2.2.1
    have h1 : barX p H L ≤ CFSG.layer Q := by
      refine le_sSup ?_
      exact (CFSG.isComponent_iff_open _).2 hLc
    have h2 := CFSG.LocalCores.fitting_layer_commute (G := Q)
    have h3 : CFSG.pCore p Q ≤ CFSG.fittingSubgroup Q := by
      have hnil : Group.IsNilpotent (CFSG.pCore p Q) :=
        (CFSG.pCore_isPGroup (p := p) (G := Q)).isNilpotent
      exact (CFSG.LocalCores.fitting_characteristic.2.2) _ CFSG.pCore_normal hnil
    have h4 : CFSG.fittingSubgroup Q ≤ Subgroup.centralizer (CFSG.layer Q : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2
    have h5 : CFSG.layer Q ≤ Subgroup.centralizer (CFSG.fittingSubgroup Q : Set Q) :=
      Subgroup.le_centralizer_iff.1 h4
    exact h1.trans (h5.trans (Subgroup.centralizer_le (hTb.trans h3)))
  set D : Subgroup G := ((Subgroup.centralizer (barX p H T : Set Q)).comap π).map H.subtype
    with hD
  have hLD : GLAPLayer p H ≤ D := by
    refine sSup_le fun L hL => ?_
    intro l hl
    refine ⟨⟨l, hL.1 hl⟩, ?_, rfl⟩
    exact hcomm L hL ⟨⟨l, hL.1 hl⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩
  rw [Subgroup.commutator_le]
  intro g hg t ht
  obtain ⟨g', hg', rfl⟩ := hLD hg
  have htH : t ∈ H := hTH ht
  have hmem : π ⟨t, htH⟩ ∈ barX p H T := ⟨⟨t, htH⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.1 hg' _ hmem
  have h1 : π (g' * ⟨t, htH⟩ * g'⁻¹ * ⟨t, htH⟩⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [← hc]
    group
  have hz : g' * ⟨t, htH⟩ * g'⁻¹ * ⟨t, htH⟩⁻¹ ∈ GLAPPrimeCore p ↥H :=
    (QuotientGroup.eq_one_iff _).1 h1
  refine ⟨g' * ⟨t, htH⟩ * g'⁻¹ * ⟨t, htH⟩⁻¹, hz, ?_⟩
  simp [commutatorElement_def]

theorem l28b_gLAPPrimeCoreOf_top_eq_bot {Y : Type*} [Group Y] {p : ℕ}
    (hO : GLAPPrimeCore p Y = ⊥) : GLAPPrimeCoreOf p (⊤ : Subgroup Y) = ⊥ := by
  have h5 := glaPPrimeCore_map_iso p (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y)
  rw [hO] at h5
  have h6 : GLAPPrimeCore p ↥(⊤ : Subgroup Y) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _
      (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).injective).1 h5
  unfold GLAPPrimeCoreOf
  rw [h6, Subgroup.map_bot]

theorem l28b_glaPLayer_top_eq_layer {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hO : GLAPPrimeCore p Y = ⊥) :
    GLAPLayer p (⊤ : Subgroup Y) = CFSG.ComponentClassification.Layer.subgroup Y := by
  have hotop : GLAPPrimeCoreOf p (⊤ : Subgroup Y) = ⊥ := l28b_gLAPPrimeCoreOf_top_eq_bot hO
  have hOt : GLAPPrimeCore p ↥(⊤ : Subgroup Y) = ⊥ := by
    have h5 := glaPPrimeCore_map_iso p (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y)
    rw [hO] at h5
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).injective).1 h5
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    obtain ⟨-, hsn, hcomp, -⟩ := hL
    have hLb : GLAPPrimeCore p ↥L = ⊥ := by
      have h1 : GLAPPrimeCoreOf p L ≤ ⊥ := hotop ▸
        CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal p hsn
      refine (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 (le_bot_iff.1 h1)
    have e : ↥L ≃* ↥(barX p ⊤ L) :=
      (QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq hLb.symm)).trans (quotEquivBarX hp le_top hsn)
    have hq : CFSG.Open.IsQuasisimple ↥L :=
      CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hcomp.2.2
    exact CFSG.ComponentClassification.Layer.component_le ⟨le_top, hsn, hq⟩
  · refine sSup_le fun K hK => le_sSup ?_
    set π0 := QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup Y)) with hπ0
    have hinj : Function.Injective π0 := by
      rw [← MonoidHom.ker_eq_bot_iff, hπ0, QuotientGroup.ker_mk', hOt]
    let Φ : Y ≃* ↥(⊤ : Subgroup Y) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup Y) :=
      Subgroup.topEquiv.symm.trans (MulEquiv.ofBijective π0 ⟨hinj, QuotientGroup.mk'_surjective _⟩)
    have hΦ : ∀ y : Y, Φ y = π0 ⟨y, Subgroup.mem_top y⟩ := fun y => rfl
    have hmap : ∀ J : Subgroup Y, (J.subgroupOf ⊤).map π0 = J.map (Φ : Y →* _) := by
      intro J
      ext z
      simp only [Subgroup.mem_map]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨(t : Y), Subgroup.mem_subgroupOf.1 ht, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, Subgroup.mem_top y⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
    refine ⟨le_top, hK.2.1, ?_, ?_⟩
    · show IsComponentOf ((K.subgroupOf ⊤).map π0) ⊤
      rw [hmap]
      have := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map Φ hK
      have htop : (⊤ : Subgroup Y).map
          (Φ : Y →* ↥(⊤ : Subgroup Y) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup Y)) = ⊤ :=
        Subgroup.map_top_of_surjective _ Φ.surjective
      rwa [htop] at this
    · intro J hJ hJsn heq
      change (J.subgroupOf ⊤).map π0 = (K.subgroupOf ⊤).map π0 at heq
      rw [hmap, hmap] at heq
      exact hJ.ne (Subgroup.map_injective Φ.injective heq)

end Generic

theorem l28b_isLThreeEpsOrON_of_equiv {J X : Type*} [Group J] [Group X] (e : X ≃* J)
    (h : IsSLThreeExc X ∨ IsSUThreeExc X) :
    IsLThreeEpsOrON (J ⧸ Subgroup.center J) := by
  rcases h with ⟨K, fld, fin, hK, ⟨φ⟩⟩ | ⟨K, fld, fin, q, hKq, hq, ⟨φ⟩⟩
  · refine Or.inl ⟨K, fld, fin, by omega, ⟨?_⟩⟩
    exact QuotientGroup.congr _ _ (e.symm.trans φ) (Subgroup.map_center_eq _)
  · refine Or.inr (Or.inl ⟨K, fld, fin, q, hKq, by omega, by omega, ⟨?_⟩⟩)
    exact QuotientGroup.congr _ _ (e.symm.trans φ) (Subgroup.map_center_eq _)

theorem l28b_gLBConj_le_bClosure {G : Type*} [Group G] {B L : Subgroup G} {g : G} (hg : g ∈ B) :
    GLBConj g L ≤ bClosure B L :=
  le_iSup₂ (f := fun b (_ : b ∈ B) => GLBConj b L) g hg

section Interface

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem l28b_isComponentOf_barX_conj {C B L : Subgroup G} (hBC : B ≤ C)
    (hL : GLAPComponent 3 C L) {g : G} (hg : g ∈ B) :
    IsComponentOf (barX 3 C (GLBConj g L)) (⊤ : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C)) := by
  have hCg : GLBConj g C = C := gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (hBC hg))
  have h := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL g
  rw [hCg] at h
  exact h.2.2.1

theorem l28b_isLThreeEpsOrON_barX_conj {C B L : Subgroup G} (hBC : B ≤ C)
    (hL : GLAPComponent 3 C L) (htype : IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L))
    {g : G} (hg : g ∈ B) :
    IsLThreeEpsOrON
      (↥(barX 3 C (GLBConj g L)) ⧸ Subgroup.center ↥(barX 3 C (GLBConj g L))) := by
  have hCg : GLBConj g C = C := gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (hBC hg))
  have h := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL g
  rw [hCg] at h
  have e : barOf 3 L ≃* ↥(barX 3 C (GLBConj g L)) :=
    (conjQuotEquiv 3 g L).trans (quotEquivBarX Nat.prime_three h.1 h.2.1)
  exact l28b_isLThreeEpsOrON_of_equiv e htype

omit [Finite G] in
theorem l28b_barX_bClosure_eq {C B L : Subgroup G} (hBC : B ≤ C) (hLC : L ≤ C) :
    barX 3 C (bClosure B L) =
      ⨆ J ∈ {J : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) |
        ∃ g ∈ B, J = barX 3 C (GLBConj g L)}, J := by
  have hconjC : ∀ g ∈ B, GLBConj g L ≤ C := by
    intro g hg y hy
    have hgC : g ∈ C := hBC hg
    have : g * y * g⁻¹ ∈ C := hLC ((mem_gLBConj).1 hy)
    have := C.mul_mem (C.mul_mem (C.inv_mem hgC) this) hgC
    simpa [mul_assoc] using this
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) with hπ
  set M : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) := ⨆ J ∈ {J : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) |
        ∃ g ∈ B, J = barX 3 C (GLBConj g L)}, J with hM
  apply le_antisymm
  · have hle : bClosure B L ≤ (M.comap π).map C.subtype := by
      refine iSup₂_le fun g hg y hy => ?_
      have hyC : y ∈ C := hconjC g hg hy
      refine ⟨⟨y, hyC⟩, ?_, rfl⟩
      have h1 : π ⟨y, hyC⟩ ∈ barX 3 C (GLBConj g L) :=
        ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
      exact le_iSup₂ (f := fun J (_ : J ∈ {J : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) |
        ∃ g ∈ B, J = barX 3 C (GLBConj g L)}) => J) (barX 3 C (GLBConj g L)) ⟨g, hg, rfl⟩ h1
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨t', ht', htt⟩ := hle (Subgroup.mem_subgroupOf.1 ht)
    have : t' = t := Subtype.ext htt
    subst this
    exact ht'
  · refine iSup₂_le fun J hJ => ?_
    obtain ⟨g, hg, rfl⟩ := hJ
    exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.2
      (l28b_gLBConj_le_bClosure hg (Subgroup.mem_subgroupOf.1 hx))

theorem l28b_isSubnormal_barX_bClosure {C B L : Subgroup G} (hBC : B ≤ C)
    (hL : GLAPComponent 3 C L) :
    IsSubnormal (barX 3 C (bClosure B L)) (⊤ : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C)) := by
  rw [l28b_barX_bClosure_eq hBC hL.1]
  refine isSubnormal_iSup_components _ ?_
  rintro J ⟨g, hg, rfl⟩
  exact l28b_isComponentOf_barX_conj hBC hL hg

end Interface

section HeartHelpers

variable {G : Type*} [Group G]

theorem l28b_isKGroup_of_surjective {H H' : Type*} [Group H] [Group H'] (hH : CFSG.Open.IsKGroup H)
    (f : H →* H') (hf : Function.Surjective f) : CFSG.Open.IsKGroup H' :=
  hH.of_surjective f hf


theorem l28b_le_normalizer_bClosure [Finite G] {B : Subgroup G} (L : Subgroup G) :
    B ≤ Subgroup.normalizer (bClosure B L : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  have key : ∀ b ∈ B, ∀ y ∈ GLBConj b L, g * y * g⁻¹ ∈ bClosure B L := by
    intro b hb y hy
    have hb' : b * g⁻¹ ∈ B := B.mul_mem hb (B.inv_mem hg)
    have : g * y * g⁻¹ ∈ GLBConj (b * g⁻¹) L := by
      rw [mem_gLBConj] at hy ⊢
      simpa [mul_assoc] using hy
    exact le_iSup₂ (f := fun b (_ : b ∈ B) => GLBConj b L) (b * g⁻¹) hb' this
  have hle : bClosure B L ≤ (bClosure B L).comap (MulAut.conj g).toMonoidHom :=
    iSup₂_le fun b hb y hy => by
      have := key b hb y hy
      simpa using this
  have := hle hx
  simpa using this

theorem l28b_pow_mem_of_mem_oPrimePOf [Finite G] {p : ℕ} (hp : p.Prime) {X : Subgroup G} {s : G}
    (hs : s ∈ oPrimePOf p X) : ∃ n : ℕ, s ^ (p ^ n) ∈ GLAPPrimeCoreOf p X := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht, rfl⟩ := hs
  have hpg : IsPGroup p (CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X)) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hpg ⟨_, ht⟩
  refine ⟨k, t ^ (p ^ k), ?_, rfl⟩
  have h1 : orderOf (QuotientGroup.mk' (GLAPPrimeCore p ↥X) t) = p ^ k := by
    have := Subgroup.orderOf_coe (⟨_, ht⟩ : CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X))
    rw [hk] at this
    exact this
  have h2 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) t ^ (p ^ k) = 1 := by
    rw [← h1]; exact pow_orderOf_eq_one _
  rw [← map_pow] at h2
  exact (QuotientGroup.eq_one_iff _).1 h2


theorem l28b_oPrimePOf_normal (p : ℕ) (X : Subgroup G) : ((oPrimePOf p X).subgroupOf X).Normal := by
  have h : (oPrimePOf p X).subgroupOf X = oPrimeP p ↥X :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  rw [h]
  infer_instance

theorem l28b_gLAPPrimeCoreOf_normal (p : ℕ) (X : Subgroup G) :
    ((GLAPPrimeCoreOf p X).subgroupOf X).Normal := by
  have h : (GLAPPrimeCoreOf p X).subgroupOf X = GLAPPrimeCore p ↥X :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  rw [h]
  infer_instance

theorem l28b_oPrimePOf_transfer [Finite G] {p : ℕ} (hp : p.Prime) {C : Subgroup G} {a b : G}
    (haC : a ∈ C) (hbC : b ∈ C) (ha : IsPGroup p (Subgroup.zpowers a))
    (hb : b ∈ oPrimePOf p (Subgroup.centralizer ({a} : Set G))) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩ ∈
      oPrimePOf p (Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨a, haC⟩} :
          Set (↥C ⧸ GLAPPrimeCore p ↥C))) := by
  classical
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥C) with hπ
  set H₀ : Subgroup G := Subgroup.centralizer ({a} : Set G) with hH₀
  set H₁ : Subgroup G := C ⊓ H₀ with hH₁
  have hcent : barX p C H₁ =
      Subgroup.centralizer ({π ⟨a, haC⟩} : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    have := barX_inf_centralizer hp (M := C) (L := C) (d := a) haC le_rfl
      (Subgroup.le_normalizer haC) ha
    rw [hH₁, hH₀, this, barX_self, top_inf_eq]
  rw [← hcent]
  have hbS : b ∈ oPrimePOf p H₀ ⊓ C := ⟨hb, hbC⟩
  set S₁ : Subgroup G := oPrimePOf p H₀ ⊓ C with hS₁
  set N₁ : Subgroup G := GLAPPrimeCoreOf p H₀ ⊓ C with hN₁
  have hoH : oPrimePOf p H₀ ≤ H₀ := Subgroup.map_subtype_le _
  have hgH : GLAPPrimeCoreOf p H₀ ≤ H₀ := Subgroup.map_subtype_le _
  have hS₁H : S₁ ≤ H₁ := fun s hs => ⟨hs.2, hoH hs.1⟩
  have hN₁H : N₁ ≤ H₁ := fun s hs => ⟨hs.2, hgH hs.1⟩
  have hconj : ∀ {S : Subgroup G}, ((S.subgroupOf H₀).Normal) → ∀ {s t : G}, s ∈ S → s ∈ H₀ →
      t ∈ H₀ → t * s * t⁻¹ ∈ S := by
    intro S hn s t hs hsH htH
    have := hn.conj_mem ⟨s, hsH⟩ (Subgroup.mem_subgroupOf.2 hs) ⟨t, htH⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hnormS : ∀ h ∈ barX p C S₁, ∀ k ∈ barX p C H₁, k * h * k⁻¹ ∈ barX p C S₁ := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    refine ⟨t * s * t⁻¹, ?_, by simp⟩
    obtain ⟨hs1, hsC⟩ := Subgroup.mem_subgroupOf.1 hs
    obtain ⟨htC, htH⟩ := Subgroup.mem_subgroupOf.1 ht
    refine Subgroup.mem_subgroupOf.2 ⟨?_, ?_⟩
    · exact hconj (l28b_oPrimePOf_normal p H₀) hs1 (hoH hs1) htH
    · simpa using C.mul_mem (C.mul_mem t.2 s.2) (C.inv_mem t.2)
  have hnormN : ∀ h ∈ barX p C N₁, ∀ k ∈ barX p C H₁, k * h * k⁻¹ ∈ barX p C N₁ := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    refine ⟨t * s * t⁻¹, ?_, by simp⟩
    obtain ⟨hs1, hsC⟩ := Subgroup.mem_subgroupOf.1 hs
    obtain ⟨htC, htH⟩ := Subgroup.mem_subgroupOf.1 ht
    refine Subgroup.mem_subgroupOf.2 ⟨?_, ?_⟩
    · exact hconj (l28b_gLAPPrimeCoreOf_normal p H₀) hs1 (hgH hs1) htH
    · simpa using C.mul_mem (C.mul_mem t.2 s.2) (C.inv_mem t.2)
  have hSle : barX p C S₁ ≤ barX p C H₁ := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.2 (hS₁H (Subgroup.mem_subgroupOf.1 hx))
  have hNle : barX p C N₁ ≤ barX p C H₁ := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.2 (hN₁H (Subgroup.mem_subgroupOf.1 hx))
  have hcop : Nat.Coprime p (Nat.card (barX p C N₁)) := by
    refine Nat.Coprime.coprime_dvd_right ?_ ((Nat.Prime.coprime_iff_not_dvd hp).2
      (not_dvd_card_glaPPrimeCoreOf hp H₀))
    have h1 : Nat.card (barX p C N₁) ∣ Nat.card (N₁.subgroupOf C) :=
      Subgroup.card_map_dvd (H := N₁.subgroupOf C) π
    have h2 : Nat.card (N₁.subgroupOf C) = Nat.card N₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun x (hx : x ∈ N₁) => hx.2)).toEquiv
    have h3 : Nat.card N₁ ∣ Nat.card (GLAPPrimeCoreOf p H₀) :=
      Subgroup.card_dvd_of_le (fun x (hx : x ∈ N₁) => hx.1)
    exact h1.trans (h2 ▸ h3)
  have hpow : ∀ s ∈ barX p C S₁, ∃ n : ℕ, s ^ (p ^ n) ∈ barX p C N₁ := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨hs1, hsC⟩ := Subgroup.mem_subgroupOf.1 hs
    obtain ⟨n, hn⟩ := l28b_pow_mem_of_mem_oPrimePOf hp hs1
    refine ⟨n, (s ^ (p ^ n)), Subgroup.mem_subgroupOf.2 ⟨?_, ?_⟩, by simp⟩
    · simpa using hn
    · simpa using C.pow_mem s.2 (p ^ n)
  have hmain := l28b_le_oPrimePOf_of_pow_mem hp hSle
    ((Subgroup.normal_subgroupOf_iff hSle).2 fun h k hh hk => hnormS h hh k hk) hNle
    ((Subgroup.normal_subgroupOf_iff hNle).2 fun h k hh hk => hnormN h hh k hk) hcop hpow
  exact hmain ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 hbS, rfl⟩

theorem l28b_mem_normalizer_bClosure {B L : Subgroup G} {u : G}
    (hu : ∀ g ∈ B, g * u * g⁻¹ ∈ Subgroup.normalizer (L : Set G)) [Finite G] :
    u ∈ Subgroup.normalizer (bClosure B L : Set G) := by
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  have key : ∀ b ∈ B, ∀ y ∈ GLBConj b L, u * y * u⁻¹ ∈ bClosure B L := by
    intro b hb y hy
    have : u * y * u⁻¹ ∈ GLBConj b L := by
      rw [mem_gLBConj] at hy ⊢
      have h1 := (Subgroup.mem_normalizer_iff.1 (hu b hb) (b * y * b⁻¹)).1 hy
      have : b * (u * y * u⁻¹) * b⁻¹ = (b * u * b⁻¹) * (b * y * b⁻¹) * (b * u * b⁻¹)⁻¹ := by group
      rw [this]
      exact h1
    exact le_iSup₂ (f := fun b (_ : b ∈ B) => GLBConj b L) b hb this
  have hle : bClosure B L ≤ (bClosure B L).comap (MulAut.conj u).toMonoidHom :=
    iSup₂_le fun b hb y hy => by
      have := key b hb y hy
      simpa using this
  have := hle hx
  simpa using this

theorem l28b_comm_mem_centralizer {Y : Type*} [Group Y] {K : Subgroup Y} {u z : Y}
    (hu : u ∈ Subgroup.normalizer (K : Set Y)) (hz : z ∈ Subgroup.centralizer (K : Set Y)) :
    u * z * u⁻¹ * z⁻¹ ∈ Subgroup.centralizer (K : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk1 : u⁻¹ * k * u ∈ K := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (K : Set Y)).inv_mem hu) k).1 hk
    simpa using this
  have hzk : k * z = z * k := Subgroup.mem_centralizer_iff.1 hz k hk
  have hzk1 : (u⁻¹ * k * u) * z = z * (u⁻¹ * k * u) := Subgroup.mem_centralizer_iff.1 hz _ hk1
  have e1 : z⁻¹ * k = k * z⁻¹ := by
    calc z⁻¹ * k = z⁻¹ * (k * z) * z⁻¹ := by group
      _ = z⁻¹ * (z * k) * z⁻¹ := by rw [hzk]
      _ = k * z⁻¹ := by group
  have e2 : z * (u⁻¹ * k * u) = (u⁻¹ * k * u) * z := hzk1.symm
  have : (u * z * u⁻¹ * z⁻¹) * k = k * (u * z * u⁻¹ * z⁻¹) := by
    calc (u * z * u⁻¹ * z⁻¹) * k = u * z * u⁻¹ * (z⁻¹ * k) := by group
      _ = u * z * u⁻¹ * (k * z⁻¹) := by rw [e1]
      _ = u * z * (u⁻¹ * k * u) * u⁻¹ * z⁻¹ := by group
      _ = u * (z * (u⁻¹ * k * u)) * u⁻¹ * z⁻¹ := by group
      _ = u * ((u⁻¹ * k * u) * z) * u⁻¹ * z⁻¹ := by rw [e2]
      _ = k * (u * z * u⁻¹ * z⁻¹) := by group
  exact this.symm


theorem l28b_eq_bot_of_normal_subnormal {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hO : GLAPPrimeCore p Y = ⊥) {K T : Subgroup Y} (hKsn : IsSubnormal K ⊤) (hTK : T ≤ K)
    (hTn : (T.subgroupOf K).Normal) (hcop : Nat.Coprime p (Nat.card T)) : T = ⊥ := by
  have hcop' : Nat.Coprime p (Nat.card (T.subgroupOf K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv]
    exact hcop
  have h1 : T.subgroupOf K ≤ GLAPPrimeCore p ↥K := le_sSup ⟨hTn, hcop'⟩
  have h2 : T ≤ GLAPPrimeCoreOf p K := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hTK]
    exact Subgroup.map_mono h1
  have h3 := CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal p hKsn
  have h4 : GLAPPrimeCoreOf p (⊤ : Subgroup Y) = ⊥ := by
    have h5 := glaPPrimeCore_map_iso p (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y)
    rw [hO] at h5
    have h6 : GLAPPrimeCore p ↥(⊤ : Subgroup Y) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _
        (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).injective).1 h5
    unfold GLAPPrimeCoreOf
    rw [h6, Subgroup.map_bot]
  exact le_bot_iff.1 (h2.trans (h3.trans h4.le))

theorem l28b_le_gLAPPrimeCoreOf_of_barX_eq_bot {p : ℕ} {C T : Subgroup G} (hTC : T ≤ C)
    (h : barX p C T = ⊥) : T ≤ GLAPPrimeCoreOf p C := by
  intro t ht
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨t, hTC ht⟩ ∈ barX p C T :=
    ⟨⟨t, hTC ht⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
  rw [h, Subgroup.mem_bot] at h1
  exact ⟨⟨t, hTC ht⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩

theorem l28b_card_barX_dvd {p : ℕ} {C T : Subgroup G} (hTC : T ≤ C) :
    Nat.card (barX p C T) ∣ Nat.card T := by
  have h1 : Nat.card (barX p C T) ∣ Nat.card (T.subgroupOf C) :=
    Subgroup.card_map_dvd (H := T.subgroupOf C) _
  have h2 : Nat.card (T.subgroupOf C) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv
  exact h2 ▸ h1

theorem l28b_conj_mem_of_normal {S X : Subgroup G} (hn : (S.subgroupOf X).Normal) {s t : G}
    (hs : s ∈ S) (hsX : s ∈ X) (htX : t ∈ X) : t * s * t⁻¹ ∈ S := by
  have := hn.conj_mem ⟨s, hsX⟩ (Subgroup.mem_subgroupOf.2 hs) ⟨t, htX⟩
  exact Subgroup.mem_subgroupOf.1 this

theorem l28b_le_bClosure (B L : Subgroup G) : L ≤ bClosure B L := by
  have := le_iSup₂ (f := fun b (_ : b ∈ B) => GLBConj b L) 1 B.one_mem
  rwa [gLBConj_one] at this
end HeartHelpers

theorem l28b_heartY (iA : Input23_26) (iB : Input18_2One) (iC : Input14_5Second)
    {Y : Type} [Group Y] [Finite Y] (hK : CFSG.Open.IsKGroup Y) (hO : GLAPPrimeCore 3 Y = ⊥)
    (𝒮 : Set (Subgroup Y)) (hc : ∀ J ∈ 𝒮, IsComponentOf J ⊤)
    (ht : ∀ J ∈ 𝒮, IsLThreeEpsOrON (↥J ⧸ Subgroup.center ↥J))
    (E : Subgroup Y) (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEN : E ≤ Subgroup.normalizer ((⨆ J ∈ 𝒮, J : Subgroup Y) : Set Y))
    (β : Y) (hβ : ∀ e ∈ E, e ≠ 1 → β ∈ oPrimePOf 3 (Subgroup.centralizer ({e} : Set Y))) :
    (⨆ J ∈ 𝒮, J : Subgroup Y) ≤ Subgroup.centralizer ({β} : Set Y) := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set K : Subgroup Y := ⨆ J ∈ 𝒮, J with hKdef
  set Ly := CFSG.ComponentClassification.Layer.subgroup Y with hLy
  have hM : GLAPLayer 3 (⊤ : Subgroup Y) = Ly := l28b_glaPLayer_top_eq_layer hp3 hO
  have hKL : K ≤ Ly :=
    iSup₂_le fun J hJ => CFSG.ComponentClassification.Layer.component_le (hc J hJ)
  have hLN : Ly ≤ Subgroup.normalizer (K : Set Y) := by
    refine sSup_le fun J' hJ' => ?_
    by_cases hJ𝒮 : J' ∈ 𝒮
    · exact (le_iSup₂_of_le J' hJ𝒮 le_rfl : J' ≤ K).trans Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (K : Set Y))
      refine Subgroup.le_centralizer_iff.2 (iSup₂_le fun K' hK' => ?_)
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (CFSG.ComponentClassification.LocalComponents.commute_of_ne K' J' (hc K' hK') hJ'
          (fun h => hJ𝒮 (h ▸ hK')))
  refine (iA Y hK 𝒮 hc ht E hE hE27 hEN).le.trans ?_
  refine iSup₂_le fun e he => iSup_le fun he1 => ?_
  set Cy : Subgroup Y := Subgroup.centralizer ({e} : Set Y) with hCy
  have hez : e ^ 3 = 1 := hE.2 e he
  have hpz : IsPGroup 3 (Subgroup.zpowers e) := by
    intro x
    refine ⟨1, ?_⟩
    obtain ⟨m, hm⟩ := x.2
    apply Subtype.ext
    have : (x : Y) ^ 3 = 1 := by
      rw [← hm]
      show (e ^ m) ^ 3 = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hez, one_zpow]
    simpa using this
  have hcz : Subgroup.centralizer ((Subgroup.zpowers e : Subgroup Y) : Set Y) = Cy := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  set N' : Subgroup Y := Subgroup.normalizer ((Subgroup.zpowers e : Subgroup Y) : Set Y) with hN'
  have hCN : Cy ≤ N' := by
    rw [← hcz]; exact Subgroup.centralizer_le_normalizer _
  have hCnorm : (Cy.subgroupOf N').Normal := by
    have := Subgroup.normal_subgroupOf_centralizer_normalizer
      ((Subgroup.zpowers e : Subgroup Y) : Set Y)
    rw [hcz] at this
    exact this
  have hKM : K ⊓ Cy ≤ GLAPLayer 3 (⊤ : Subgroup Y) ⊓ Cy := inf_le_inf_right _ (hM ▸ hKL)
  have hnorm : ((K ⊓ Cy).subgroupOf (GLAPLayer 3 (⊤ : Subgroup Y) ⊓ Cy)).Normal := by
    refine ⟨fun s hs n => ?_⟩
    have hs' : (s : Y) ∈ K ⊓ Cy := hs
    have hnn : (n : Y) ∈ Subgroup.normalizer (K : Set Y) := hLN (hM ▸ n.2.1)
    refine ⟨(Subgroup.mem_normalizer_iff.1 hnn _).1 hs'.1, ?_⟩
    have hnc : (n : Y) ∈ Cy := n.2.2
    have hsc : (s : Y) ∈ Cy := hs'.2
    have := Cy.mul_mem (Cy.mul_mem hnc hsc) (Cy.inv_mem hnc)
    exact this
  have h1 : GLAPLayer 3 (K ⊓ Cy) ≤ GLAPLayer 3 (GLAPLayer 3 (⊤ : Subgroup Y) ⊓ Cy) :=
    l28b_glaPLayer_le_of_normal hp3 hKM hnorm
  have h2 : GLAPLayer 3 (GLAPLayer 3 (⊤ : Subgroup Y) ⊓ Cy) = GLAPLayer 3 Cy := by
    have := iB Y hK 3 hp3 (Subgroup.zpowers e) hpz
    rwa [hcz] at this
  have h3 : GLAPLayer 3 Cy ≤ GLAPLayer 3 N' := l28b_glaPLayer_le_of_normal hp3 hCN hCnorm
  have hβC : β ∈ oPrimePOf 3 Cy := hβ e he he1
  have hβN : β ∈ oPrimePOf 3 N' := l28b_oPrimePOf_le_of_normal hp3 hCN hCnorm hβC
  have hbotN : ⁅GLAPLayer 3 N', GLAPPrimeCoreOf 3 N'⁆ = ⊥ := by
    have hne : Subgroup.zpowers e ≠ ⊥ := by
      intro h
      apply he1
      have : e ∈ Subgroup.zpowers e := Subgroup.mem_zpowers e
      rw [h] at this
      exact this
    exact iC Y hK hO (Subgroup.zpowers e) hne hpz
  have hcommN : ⁅GLAPLayer 3 N', oPrimePOf 3 N'⁆ ≤ GLAPPrimeCoreOf 3 N' :=
    l28b_commutator_glaPLayer_le hp3 N'
  set M' : Subgroup Y := GLAPLayer 3 N' with hM'
  have hperf : ⁅M', M'⁆ = M' := by
    refine le_antisymm ?_ ?_
    · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [commutatorElement_def]
      exact M'.mul_mem (M'.mul_mem (M'.mul_mem ha hb) (M'.inv_mem ha)) (M'.inv_mem hb)
    · refine sSup_le fun L hL => ?_
      have hLL := glaPComponent_perfect hL
      calc L = ⁅L, L⁆ := hLL.symm
        _ ≤ ⁅M', M'⁆ := Subgroup.commutator_mono (le_sSup hL) (le_sSup hL)
  have hzβ : Subgroup.zpowers β ≤ oPrimePOf 3 N' := Subgroup.zpowers_le.2 hβN
  set R : Subgroup Y := ⁅M', Subgroup.zpowers β⁆ with hR
  have hRO : R ≤ GLAPPrimeCoreOf 3 N' :=
    (Subgroup.commutator_mono le_rfl hzβ).trans hcommN
  have hRM : ⁅R, M'⁆ = ⊥ := by
    refine eq_bot_iff.2 ?_
    calc ⁅R, M'⁆ ≤ ⁅GLAPPrimeCoreOf 3 N', M'⁆ := Subgroup.commutator_mono hRO le_rfl
      _ = ⁅M', GLAPPrimeCoreOf 3 N'⁆ := Subgroup.commutator_comm _ _
      _ = ⊥ := hbotN
      _ ≤ ⊥ := le_rfl
  have hr1 : ⁅⁅M', Subgroup.zpowers β⁆, M'⁆ = ⊥ := hRM
  have hr2 : ⁅⁅Subgroup.zpowers β, M'⁆, M'⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (Subgroup.zpowers β) M']
    exact hRM
  have h3s : ⁅⁅M', M'⁆, Subgroup.zpowers β⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate hr1 hr2
  have hMc : M' ≤ Subgroup.centralizer ((Subgroup.zpowers β : Subgroup Y) : Set Y) := by
    rw [← hperf]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3s
  have hMβ : M' ≤ Subgroup.centralizer ({β} : Set Y) :=
    hMc.trans (Subgroup.centralizer_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subgroup.mem_zpowers x))
  rw [h2] at h1
  exact h1.trans (h3.trans hMβ)

theorem l28b_heart_claim (iA : Input23_26) (iB : Input18_2One) (iC : Input14_5Second)
    {G : Type} [Group G] [Finite G] {m : ℕ} (hS : GLStanding G m 3)
    {B A : Subgroup G} (hB : IsElemAbelian 3 B) {k : ℕ} (hk : 3 ≤ k) (hA : IsEkIn 3 k B A)
    {x : G} (hx : x ∈ B) (hx1 : x ≠ 1) {b : G} (hbA : b ∈ A)
    (hcore : ∀ a ∈ A, a ≠ 1 → b ∈ oPrimePOf 3 (Subgroup.centralizer ({a} : Set G)))
    {L : Subgroup G} (hL : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) L)
    (htype : IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L)) :
    barX 3 (Subgroup.centralizer ({x} : Set G)) (Subgroup.zpowers b) ≤
      Subgroup.centralizer
        (barX 3 (Subgroup.centralizer ({x} : Set G)) (bClosure B L) :
          Set (↥(Subgroup.centralizer ({x} : Set G)) ⧸
            GLAPPrimeCore 3 ↥(Subgroup.centralizer ({x} : Set G)))) := by
  classical
  have := hS.simple
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  obtain ⟨hAB, hAe, hAcard⟩ := hA
  have hBC : B ≤ C := le_centralizer_of_mem hB hx
  have hCne : C ≠ ⊤ := centralizer_ne_top_of_simple hS.nonabelian hx1
  have hKC : CFSG.Open.IsKGroup ↥C := isKGroup_of_isKProper hS.kProper hCne
  have hKY : CFSG.Open.IsKGroup (↥C ⧸ GLAPPrimeCore 3 ↥C) :=
    l28b_isKGroup_of_surjective hKC (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hOY : GLAPPrimeCore 3 (↥C ⧸ GLAPPrimeCore 3 ↥C) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
  have hLC : L ≤ C := hL.1
  set 𝒮 : Set (Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C)) :=
    {J | ∃ g ∈ B, J = barX 3 C (GLBConj g L)} with h𝒮
  have hc : ∀ J ∈ 𝒮, IsComponentOf J ⊤ := by
    rintro J ⟨g, hg, rfl⟩
    exact l28b_isComponentOf_barX_conj hBC hL hg
  have ht : ∀ J ∈ 𝒮, IsLThreeEpsOrON (↥J ⧸ Subgroup.center ↥J) := by
    rintro J ⟨g, hg, rfl⟩
    exact l28b_isLThreeEpsOrON_barX_conj hBC hL htype hg
  have hKeq : barX 3 C (bClosure B L) = ⨆ J ∈ 𝒮, J := l28b_barX_bClosure_eq hBC hLC
  obtain ⟨A₃, hA₃A, hA₃e, hA₃card⟩ := exists_le_isElemAbelian_card (p := 3) hAe (n := 3)
    (by rw [hAcard]; exact pow_dvd_pow 3 hk)
  have hA₃B : A₃ ≤ B := hA₃A.trans hAB
  have hA₃C : A₃ ≤ C := hA₃B.trans hBC
  have hA₃p : IsPGroup 3 A₃ := fun y =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hA₃e.2 y y.2)⟩
  set E : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) := barX 3 C A₃ with hE
  have hEe : IsElemAbelian 3 E := isElemAbelian_barX hA₃e
  have hE27 : Nat.card E = 27 := by
    set f := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)).comp (A₃.subgroupOf C).subtype with hf
    have hfi := injective_barX_comp hp3 hA₃p hA₃C
    have hrange : f.range = E := by
      rw [hf, hE, MonoidHom.range_comp, Subgroup.range_subtype]
      rfl
    have h1 : Nat.card E = Nat.card ↥(A₃.subgroupOf C) := by
      rw [← hrange]
      exact (Nat.card_congr (Equiv.ofInjective f hfi)).symm
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₃C).toEquiv, hA₃card]
    norm_num
  have hEN : E ≤ Subgroup.normalizer
      ((⨆ J ∈ 𝒮, J : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C)) : Set _) := by
    rw [← hKeq]
    exact barX_le_normalizer (fun a ha => l28b_le_normalizer_bClosure L (hA₃B ha))
  have hbB : b ∈ B := hAB hbA
  have hbC : b ∈ C := hBC hbB
  set β : ↥C ⧸ GLAPPrimeCore 3 ↥C := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨b, hbC⟩ with hβ
  have hβ' : ∀ e ∈ E, e ≠ 1 → β ∈ oPrimePOf 3 (Subgroup.centralizer ({e} : Set _)) := by
    rintro _ ⟨a', ha', rfl⟩ hne
    have haA₃ : (a' : G) ∈ A₃ := Subgroup.mem_subgroupOf.1 ha'
    have ha1 : (a' : G) ≠ 1 := by
      intro h
      apply hne
      have : a' = 1 := Subtype.ext h
      rw [this, map_one]
    have hbo := hcore a' (hA₃A haA₃) ha1
    have hpa : IsPGroup 3 (Subgroup.zpowers (a' : G)) := by
      intro y
      refine ⟨1, ?_⟩
      obtain ⟨n, hn⟩ := y.2
      apply Subtype.ext
      have : (y : G) ^ 3 = 1 := by
        rw [← hn]
        show ((a' : G) ^ n) ^ 3 = 1
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hA₃e.2 _ haA₃, one_zpow]
      simpa using this
    exact l28b_oPrimePOf_transfer hp3 a'.2 hbC hpa hbo
  have hY := l28b_heartY iA iB iC hKY hOY 𝒮 hc ht E hEe hE27 hEN β hβ'
  rw [hKeq]
  rintro _ ⟨t, ht', rfl⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 ht')
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyc : y * β = β * y := Subgroup.mem_centralizer_singleton_iff.1 (hY hy)
  have htn : t = (⟨b, hbC⟩ : ↥C) ^ n := Subtype.ext (by simpa using hn.symm)
  rw [htn, map_zpow]
  exact ((Commute.zpow_right (show Commute y β from hyc) n)).eq

theorem l28b_key_claim (iA : Input23_26) (iB : Input18_2One) (iC : Input14_5Second)
    {G : Type} [Group G] [Finite G] {m : ℕ} (hS : GLStanding G m 3)
    {B A D : Subgroup G} (hB : IsElemAbelian 3 B) {k : ℕ} (hk : 3 ≤ k) (hA : IsEkIn 3 k B A)
    (hD : IsEkIn 3 2 B D) {x : G} (hx : x ∈ B) (hx1 : x ≠ 1) {b : G} (hb : b ∈ B) (hbA : b ∈ A)
    (hcore : ∀ a ∈ A, a ≠ 1 → b ∈ oPrimePOf 3 (Subgroup.centralizer ({a} : Set G)))
    {L : Subgroup G} (hsetup : Lemma24Setup 3 B D x L) (hconc : Lemma24Conclusion B D x L) :
    ¬ delta2At 3 B D b ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
  classical
  have := hS.simple
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  intro hcontra
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  set Cb : Subgroup G := Subgroup.centralizer ({b} : Set G) with hCb
  set P : Subgroup G := GLAPPrimeCoreOf 3 C with hP
  set Pb : Subgroup G := GLAPPrimeCoreOf 3 Cb with hPb
  have hBC : B ≤ C := le_centralizer_of_mem hB hx
  have hbC : b ∈ C := hBC hb
  have hL : GLAPComponent 3 C L := hsetup.isComp
  have hLC : L ≤ C := hL.1
  set Kst : Subgroup G := bClosure B L with hKst
  have hKstC : Kst ≤ C := by
    refine iSup₂_le fun g hg y hy => ?_
    have hgC : g ∈ C := hBC hg
    have : g * y * g⁻¹ ∈ C := hLC ((mem_gLBConj).1 hy)
    have := C.mul_mem (C.mul_mem (C.inv_mem hgC) this) hgC
    simpa [mul_assoc] using this
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) with hπ
  set Kt : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) := barX 3 C Kst with hKt
  have hHC := l28b_heart_claim iA iB iC hS hB hk hA hx hx1 hbA hcore hL hconc.2.1
  set W : Subgroup G := GLADelta 3 D ⊓ C with hW
  set U : Subgroup G := delta2At 3 B D x with hU
  have hUdef : U = ⁅W, B⁆ := rfl
  have hUC : U ≤ C := by
    refine Subgroup.commutator_le.2 fun w hw e he => ?_
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem hw.2 (hBC he)) (C.inv_mem hw.2)) (C.inv_mem (hBC he))
  have hUΔ : U ≤ GLADelta 3 D := delta2At_le_gLADelta hB hD.1 x
  have hBW : B ≤ Subgroup.normalizer (W : Set G) := fun g hg =>
    mem_normalizer_inf (le_normalizer_gLADelta hB hD.1 hg) (Subgroup.le_normalizer (hBC hg))
  have hDne : D ≠ ⊥ := by
    intro h
    have h1 := hD.2.2
    rw [h, Subgroup.card_bot] at h1
    have h2 : 1 < 3 ^ 2 := by norm_num
    omega
  have hWcop : Nat.Coprime 3 (Nat.card W) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (inf_le_left : W ≤ GLADelta 3 D))
      (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLADelta hp3 hDne)
  have hdecomp : U ≤ ⁅U ⊓ Cb, B⁆ ⊔ ⁅U, Subgroup.zpowers b⁆ :=
    l28b_commutator_decomp hB hBW hWcop hb
  have hUN : ∀ g ∈ B, ∀ u ∈ U, g * u * g⁻¹ ∈ U := fun g hg u hu =>
    conj_mem_commutator hBW hg hu
  have hUL : U ≤ Subgroup.normalizer (L : Set G) := hconc.2.2.1.2.1
  have hUK : U ≤ Subgroup.normalizer (Kst : Set G) := fun u hu =>
    l28b_mem_normalizer_bClosure (fun g hg => hUL (hUN g hg u hu))
  have hOY : GLAPPrimeCore 3 (↥C ⧸ GLAPPrimeCore 3 ↥C) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
  have hKtsn : IsSubnormal Kt ⊤ := l28b_isSubnormal_barX_bClosure hBC hL
  set R : Subgroup G := ((Subgroup.centralizer (Kt : Set (↥C ⧸ GLAPPrimeCore 3 ↥C))).comap π).map
    C.subtype with hR
  have hRmem : ∀ u : G, ∀ hu : u ∈ C,
      π ⟨u, hu⟩ ∈ Subgroup.centralizer (Kt : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) → u ∈ R :=
    fun u hu h => ⟨⟨u, hu⟩, h, rfl⟩
  have hRmem' : ∀ u ∈ R, ∃ hu : u ∈ C,
      π ⟨u, hu⟩ ∈ Subgroup.centralizer (Kt : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t.2, ht⟩
  have hZR : ⁅U, Subgroup.zpowers b⁆ ≤ R := by
    refine Subgroup.commutator_le.2 fun u hu z hz => ?_
    have huC := hUC hu
    have hzB : z ∈ B := (Subgroup.zpowers_le.2 hb) hz
    have hzC : z ∈ C := hBC hzB
    have hcC : u * z * u⁻¹ * z⁻¹ ∈ C :=
      C.mul_mem (C.mul_mem (C.mul_mem huC hzC) (C.inv_mem huC)) (C.inv_mem hzC)
    refine hRmem (⁅u, z⁆) hcC ?_
    show π ⟨u * z * u⁻¹ * z⁻¹, hcC⟩ ∈ _
    have e : π ⟨u * z * u⁻¹ * z⁻¹, hcC⟩ =
        π ⟨u, huC⟩ * π ⟨z, hzC⟩ * (π ⟨u, huC⟩)⁻¹ * (π ⟨z, hzC⟩)⁻¹ := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    rw [e]
    refine l28b_comm_mem_centralizer (K := Kt) ?_ ?_
    · exact barX_le_normalizer hUK ⟨⟨u, huC⟩, Subgroup.mem_subgroupOf.2 hu, rfl⟩
    · exact hHC ⟨⟨z, hzC⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
  have hbN : b ∈ Subgroup.normalizer (Kst : Set G) := l28b_le_normalizer_bClosure L hb
  have hbp : IsPGroup 3 (Subgroup.zpowers b) := by
    intro y
    refine ⟨1, ?_⟩
    obtain ⟨n, hn⟩ := y.2
    apply Subtype.ext
    have : (y : G) ^ 3 = 1 := by
      rw [← hn]
      show (b ^ n) ^ 3 = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hB.2 b hb, one_zpow]
    simpa using this
  have hcov : barX 3 C (Kst ⊓ Cb) = Kt := by
    have h := barX_inf_centralizer hp3 (M := C) (L := Kst) (d := b) hbC hKstC hbN hbp
    rw [hCb, h]
    refine inf_eq_left.2 fun kt hkt => ?_
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    exact Subgroup.mem_centralizer_iff.1
      (hHC ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers b), rfl⟩) kt hkt
  have hPbC : Pb ≤ Cb := Subgroup.map_subtype_le _
  have hTP : Kst ⊓ Pb ≤ P := by
    have hTC : Kst ⊓ Pb ≤ C := inf_le_left.trans hKstC
    refine l28b_le_gLAPPrimeCoreOf_of_barX_eq_bot hTC ?_
    have hTK : barX 3 C (Kst ⊓ Pb) ≤ Kt :=
      Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.2
        (Subgroup.mem_subgroupOf.1 hx).1
    refine l28b_eq_bot_of_normal_subnormal hOY hKtsn hTK ?_ ?_
    · refine (Subgroup.normal_subgroupOf_iff hTK).2 fun h kk hh hk => ?_
      rw [← hcov] at hk
      obtain ⟨t, ht, rfl⟩ := hh
      obtain ⟨w, hw, rfl⟩ := hk
      obtain ⟨htK, htP⟩ := Subgroup.mem_subgroupOf.1 ht
      obtain ⟨hwK, hwCb⟩ := Subgroup.mem_subgroupOf.1 hw
      refine ⟨w * t * w⁻¹, Subgroup.mem_subgroupOf.2 ⟨?_, ?_⟩, by simp⟩
      · exact Kst.mul_mem (Kst.mul_mem hwK htK) (Kst.inv_mem hwK)
      · exact l28b_conj_mem_of_normal (l28b_gLAPPrimeCoreOf_normal 3 Cb) htP (hPbC htP) hwCb
    · refine Nat.Coprime.coprime_dvd_right ?_ ((Nat.Prime.coprime_iff_not_dvd hp3).2
        (not_dvd_card_glaPPrimeCoreOf hp3 Cb))
      exact (l28b_card_barX_dvd hTC).trans (Subgroup.card_dvd_of_le inf_le_right)
  have hUPR : ∀ y ∈ U ⊓ Pb, y ∈ R := by
    intro y hy
    have hyU : y ∈ U := hy.1
    have hyP : y ∈ Pb := hy.2
    have hyC : y ∈ C := hUC hyU
    refine hRmem y hyC ?_
    rw [Subgroup.mem_centralizer_iff]
    intro kt hkt
    rw [← hcov] at hkt
    obtain ⟨w, hw, rfl⟩ := hkt
    obtain ⟨hwK, hwCb⟩ := Subgroup.mem_subgroupOf.1 hw
    have hwC : (w : G) ∈ C := w.2
    have hc1 : (w : G) * y * (w : G)⁻¹ ∈ Pb :=
      l28b_conj_mem_of_normal (l28b_gLAPPrimeCoreOf_normal 3 Cb) hyP (hPbC hyP) hwCb
    have hc2 : (w : G) * y * (w : G)⁻¹ * y⁻¹ ∈ Pb := Pb.mul_mem hc1 (Pb.inv_mem hyP)
    have hc3 : (w : G) * y * (w : G)⁻¹ * y⁻¹ ∈ Kst := by
      have h1 : y * (w : G)⁻¹ * y⁻¹ ∈ Kst :=
        (Subgroup.mem_normalizer_iff.1 (hUK hyU) _).1 (Kst.inv_mem hwK)
      have := Kst.mul_mem hwK h1
      simpa [mul_assoc] using this
    obtain ⟨c, hcP, hcc⟩ := hTP ⟨hc3, hc2⟩
    have hcc' : c = w * ⟨y, hyC⟩ * w⁻¹ * ⟨y, hyC⟩⁻¹ := Subtype.ext hcc
    have h1 : π c = 1 := (QuotientGroup.eq_one_iff _).2 hcP
    rw [hcc', map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π w * π ⟨y, hyC⟩
        = (π w * π ⟨y, hyC⟩ * (π w)⁻¹ * (π ⟨y, hyC⟩)⁻¹) * (π ⟨y, hyC⟩ * π w) := by group
      _ = π ⟨y, hyC⟩ * π w := by rw [h1, one_mul]
  have hBU : B ≤ Subgroup.normalizer (U : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hUN g hg h hh, fun hh => ?_⟩
    have := hUN g⁻¹ (B.inv_mem hg) _ hh
    simpa [mul_assoc] using this
  have hYR : ⁅U ⊓ Cb, B⁆ ≤ R := by
    intro y hy
    refine hUPR y ⟨?_, hcontra ?_⟩
    · exact commutator_le_of_normalizer hBU
        (Subgroup.commutator_mono inf_le_left le_rfl hy)
    · exact Subgroup.commutator_mono (inf_le_inf_right _ hUΔ) le_rfl hy
  have hUR : U ≤ R := hdecomp.trans (sup_le hYR hZR)
  have hfin : ⁅L, U⁆ ≤ P := by
    refine Subgroup.commutator_le.2 fun l hl u hu => ?_
    obtain ⟨huC, hπu⟩ := hRmem' u (hUR hu)
    have hlC := hLC hl
    have hlK : π ⟨l, hlC⟩ ∈ Kt :=
      ⟨⟨l, hlC⟩, Subgroup.mem_subgroupOf.2 (l28b_le_bClosure B L hl), rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.1 hπu (π ⟨l, hlC⟩) hlK
    have hcC : l * u * l⁻¹ * u⁻¹ ∈ C :=
      C.mul_mem (C.mul_mem (C.mul_mem hlC huC) (C.inv_mem hlC)) (C.inv_mem huC)
    refine ⟨⟨l * u * l⁻¹ * u⁻¹, hcC⟩, (QuotientGroup.eq_one_iff _).1 ?_, rfl⟩
    have h : π (⟨l, hlC⟩ * ⟨u, huC⟩ * ⟨l, hlC⟩⁻¹ * ⟨u, huC⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc π ⟨l, hlC⟩ * π ⟨u, huC⟩ * (π ⟨l, hlC⟩)⁻¹ * (π ⟨u, huC⟩)⁻¹
          = (π ⟨u, huC⟩ * π ⟨l, hlC⟩) * (π ⟨l, hlC⟩)⁻¹ * (π ⟨u, huC⟩)⁻¹ := by rw [hcomm]
        _ = 1 := by group
    exact h
  exact hsetup.not_centralizes hfin

theorem lemma28_of_inputs (h24 : Lemma24) (iA : Input23_26) (iB : Input18_2One)
    (iC : Input14_5Second) : Lemma28 := by
  intro G _ _ m hS B hB hrank b hb hb1 A k hk hA hT hbA hcore hnorm
  refine ⟨lemma28_isBZeroMax hS hB hrank hb hb1 hk hA hT hbA hcore, ?_⟩
  have hBZ := lemma28_isBZeroMax hS hB hrank hb hb1 hk hA hT hbA hcore
  have hB1 : IsBOneMax 3 B :=
    CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (by norm_num) hBZ
  intro D hD x hx hx1
  by_contra hX
  have hnwb : ¬ IsWeaklyBalancedWrt 3 2 B := fun h => hX (h D hD x hx hx1)
  have hX' : ¬ delta2At 3 B D x ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G)) := hX
  obtain ⟨-, ⟨L, hLc, hLn⟩, hconc⟩ := h24 G m 3 hS B hB1 hnwb D hD x hx hx1 hX'
  have hsetup : Lemma24Setup 3 B D x L := ⟨hB1, hD, hx, hx1, hX', hLc, hLn⟩
  have hconcL := hconc L hsetup
  have hkey := l28b_key_claim iA iB iC hS hB hk hA hD hx hx1 hb hbA hcore hsetup hconcL
  obtain ⟨-, ⟨L', hL'c, hL'n⟩, hconc'⟩ := h24 G m 3 hS B hB1 hnwb D hD b hb hb1 hkey
  have hidx := (hconc' L' ⟨hB1, hD, hb, hb1, hkey, hL'c, hL'n⟩).1
  rw [Subgroup.relIndex_eq_one.2 (hnorm L' hL'c)] at hidx
  exact absurd hidx (by norm_num)

end CFSG.HardMathSupport.Solomon.LocalBalance
