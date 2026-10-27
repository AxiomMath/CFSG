module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.Lemma413
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_10Reduced

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

section Lambda

variable {Λ : Type} [Group Λ] [Finite Λ]

theorem i1810S_centralizer_sup_normal {q : ℕ} [Fact q.Prime] (V X Q : Subgroup Λ) [hVn : V.Normal]
    [hXn : X.Normal] (hXV : X ≤ V) (hQX : Q ≤ X) (hQq : IsPGroup q Q)
    (hQi : ¬ q ∣ Q.relIndex X) : (Subgroup.centralizer (Q : Set Λ) ⊔ V).Normal := by
  set C : Subgroup Λ := Subgroup.centralizer (Q : Set Λ) with hCdef
  have hQX' : IsPGroup q (Q.subgroupOf X) :=
    hQq.of_equiv (Subgroup.subgroupOfEquivOfLe hQX).symm
  set QX : Sylow q X := hQX'.toSylow hQi with hQXdef
  have hQXmap : (QX : Subgroup X).map X.subtype = Q := by
    change (Q.subgroupOf X).map X.subtype = Q
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hQX]
  have hFr : Subgroup.normalizer (Q : Set Λ) ⊔ X = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top QX
    rwa [hQXmap] at h
  refine i1810_sup_normal_of_conj fun g c hc => ?_
  have hg : g ∈ ((Subgroup.normalizer (Q : Set Λ) ⊔ X : Subgroup Λ) : Set Λ) := by
    rw [hFr]
    exact Subgroup.mem_top g
  rw [Subgroup.mul_normal] at hg
  obtain ⟨n, hn, x, hx, rfl⟩ := hg
  have h1 : n * c * n⁻¹ ∈ C := by
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : n⁻¹ * y * n ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) y).1 hy
      simpa using this
    have hcy := Subgroup.mem_centralizer_iff.1 hc _ hy'
    calc y * (n * c * n⁻¹) = n * ((n⁻¹ * y * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * y * n)) * n⁻¹ := by rw [hcy]
      _ = n * c * n⁻¹ * y := by group
  have h2 : x * c * x⁻¹ * c⁻¹ ∈ V := by
    apply hXV
    have h' := X.mul_mem hx (hXn.conj_mem _ (X.inv_mem hx) c)
    simpa [mul_assoc] using h'
  have h3 : n * (x * c * x⁻¹ * c⁻¹) * n⁻¹ ∈ V := hVn.conj_mem _ h2 n
  have heq : n * x * c * (n * x)⁻¹ =
      (n * (x * c * x⁻¹ * c⁻¹) * n⁻¹) * (n * c * n⁻¹) := by group
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h3) (Subgroup.mem_sup_left h1)

theorem i1810S_false_reduced (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hΛ : CFSG.Open.IsKGroup Λ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (V : Subgroup Λ)
    [hVn : V.Normal] (hVp : Nat.Coprime p (Nat.card V))
    (hperf : ⁅(⊤ : Subgroup Λ), (⊤ : Subgroup Λ)⁆ = ⊤)
    (hpp : ∀ M : Subgroup Λ, M.Normal → ¬ p ∣ M.index → M = ⊤)
    (X : Subgroup Λ) [hXn : X.Normal] (hXV : X ≤ V) (hXX : ⁅X, (⊤ : Subgroup Λ)⁆ = X)
    (Q : Subgroup Λ) (hQX : Q ≤ X) (hQq : IsPGroup q Q) (hQi : ¬ q ∣ Q.relIndex X)
    (hOq : ∀ N : Subgroup Λ, N.Normal → N ≤ X → Nat.Coprime q (Nat.card N) → N = ⊥)
    (hqX : q ∣ Nat.card X)
    (hCV : Subgroup.centralizer (Q : Set Λ) ⊔ V = ⊤) : False := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact p.Prime := ⟨hp⟩
  set C : Subgroup Λ := Subgroup.centralizer (Q : Set Λ) with hCdef
  have hmin : ∀ M : Subgroup Λ, M.Normal → M ⊔ V = ⊤ → M = ⊤ := by
    intro M hM hMV
    apply hpp M hM
    have h1 := Subgroup.relIndex_sup_right (H := V) (K := M)
    rw [sup_comm, hMV, Subgroup.relIndex_top_right] at h1
    rw [h1]
    exact fun hd =>
      (Nat.Prime.coprime_iff_not_dvd hp).1 hVp (hd.trans (Subgroup.relIndex_dvd_card _ _))
  have hQX' : IsPGroup q (Q.subgroupOf X) :=
    hQq.of_equiv (Subgroup.subgroupOfEquivOfLe hQX).symm
  set QX : Sylow q X := hQX'.toSylow hQi with hQXdef
  obtain ⟨n, hn⟩ := i1810_exists_derivedSeries_succ_eq C
  set D₀ : Subgroup C := derivedSeries C n with hD₀
  have : Group.IsPerfect D₀ :=
    Subgroup.isPerfect_iff.2 (by rw [hD₀, ← derivedSeries_succ, hn])
  have hDV : ∀ g : Λ, ∃ d : D₀, ((d : C) : Λ)⁻¹ * g ∈ V := by
    set f : C →* Λ ⧸ V := (QuotientGroup.mk' V).comp C.subtype with hf
    have hfs : Function.Surjective f := by
      intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      have hg : g ∈ ((C ⊔ V : Subgroup Λ) : Set Λ) := by
        rw [hCV]
        exact Subgroup.mem_top g
      rw [Subgroup.mul_normal] at hg
      obtain ⟨c, hc, v, hv, rfl⟩ := hg
      refine ⟨⟨c, hc⟩, ?_⟩
      change ((c : Λ) : Λ ⧸ V) = ((c * v : Λ) : Λ ⧸ V)
      rw [QuotientGroup.eq]
      simpa using hv
    have htop : derivedSeries (Λ ⧸ V) n = ⊤ := by
      refine i1810_derivedSeries_eq_top ?_ n
      rw [← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective V),
        ← Subgroup.map_commutator, hperf]
    intro g
    have hmem : ((g : Λ) : Λ ⧸ V) ∈ D₀.map f := by
      have h := derivedSeries_le_map_derivedSeries hfs n
      rw [htop] at h
      exact h (Subgroup.mem_top _)
    obtain ⟨d, hd, hdg⟩ := hmem
    refine ⟨⟨d, hd⟩, ?_⟩
    rw [← QuotientGroup.eq]
    exact hdg
  have hXK : CFSG.Open.IsKGroup X := CFSG.LocalAnalysis.GLTheoremB.isKGroup_subgroup' hΛ X
  have hXp : Nat.Coprime p (Nat.card X) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hXV) hVp
  have hO : CFSG.pPrimeCore q X = ⊥ := by
    have hNn := i1810_map_normal_of_characteristic (N := X) (CFSG.pPrimeCore q X)
    have hN := hOq _ hNn (Subgroup.map_subtype_le _) (by
      rw [Subgroup.card_map_of_injective X.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card)
    exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 hN
  set ρ : D₀ →* MulAut X := (MulAut.conjNormal (H := X)).comp (C.subtype.comp D₀.subtype)
    with hρ
  have hρapp : ∀ (d : D₀) (x : X),
      ((ρ d x : X) : Λ) = ((d : C) : Λ) * x * ((d : C) : Λ)⁻¹ := by
    intro d x
    simp [hρ, MulAut.conjNormal_apply]
  have hρQ : ∀ d : D₀, ∀ x ∈ (QX : Subgroup X), ρ d x = x := by
    intro d x hx
    apply Subtype.ext
    rw [hρapp]
    have hxQ : (x : Λ) ∈ Q := hx
    have hdx := Subgroup.mem_centralizer_iff.1 (d : C).2 _ hxQ
    rw [← hdx]
    group
  have hfixD : ∀ (d : D₀) (k : ℕ), d ^ p ^ k = 1 →
      ((d : C) : Λ) ∈ Subgroup.centralizer (X : Set Λ) := by
    intro d k hd
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := i1810_fixed_of_pElement hSch hXK hXp hO QX ρ hρQ hd ⟨x, hx⟩
    have h' := congrArg Subtype.val h
    rw [hρapp] at h'
    calc x * ((d : C) : Λ) = (((d : C) : Λ) * x * ((d : C) : Λ)⁻¹) * ((d : C) : Λ) := by
          rw [h']
      _ = ((d : C) : Λ) * x := by group
  set M' : Subgroup Λ := Subgroup.centralizer (X : Set Λ) ⊔ V with hM'
  have hCXn : (Subgroup.centralizer (X : Set Λ)).Normal := inferInstance
  have hM'idx : ¬ p ∣ M'.index := by
    intro hdvd
    rw [Subgroup.index] at hdvd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hdvd
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨d, hdg⟩ := hDV g
    have hgd : (g : Λ ⧸ M') = (((d : C) : Λ) : Λ ⧸ M') := by
      rw [QuotientGroup.eq]
      have h' : g⁻¹ * ((d : C) : Λ) = (((d : C) : Λ)⁻¹ * g)⁻¹ := by group
      rw [h']
      exact M'.inv_mem (Subgroup.mem_sup_right hdg)
    obtain ⟨e, m, hm, hdm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos d).ne' p hp.ne_one
    have hdm' : (d ^ m) ^ p ^ e = 1 := by
      rw [← pow_mul, mul_comm, ← hdm, pow_orderOf_eq_one]
    have hcen := hfixD (d ^ m) e hdm'
    have h1 : (((d : C) : Λ) : Λ ⧸ M') ^ m = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      apply Subgroup.mem_sup_left
      simpa using hcen
    rw [hgd] at hy
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hy] at h2
    exact hm h2
  have hM'top : M' = ⊤ := hpp M' (Subgroup.sup_normal _ _) hM'idx
  have hCX : Subgroup.centralizer (X : Set Λ) = ⊤ := hmin _ hCXn hM'top
  have hXc : ⁅X, (⊤ : Subgroup Λ)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer, hCX]
  have hX1 : X = ⊥ := by rw [← hXX]; exact hXc
  rw [hX1, Subgroup.card_bot] at hqX
  exact hq.one_lt.ne' (Nat.dvd_one.1 hqX)

theorem i1810S_false (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hΛ : CFSG.Open.IsKGroup Λ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (V : Subgroup Λ)
    [hVn : V.Normal] (hVp : Nat.Coprime p (Nat.card V))
    (hperf : ⁅(⊤ : Subgroup Λ), (⊤ : Subgroup Λ)⁆ = ⊤)
    (hpp : ∀ M : Subgroup Λ, M.Normal → ¬ p ∣ M.index → M = ⊤)
    (X : Subgroup Λ) [hXn : X.Normal] (hXV : X ≤ V) (hXX : ⁅X, (⊤ : Subgroup Λ)⁆ = X)
    (Q : Subgroup Λ) (hQX : Q ≤ X) (hQq : IsPGroup q Q) (hQi : ¬ q ∣ Q.relIndex X)
    (hqX : q ∣ Nat.card X)
    (hCV : Subgroup.centralizer (Q : Set Λ) ⊔ V = ⊤) : False := by
  have : Fact q.Prime := ⟨hq⟩
  set N : Subgroup Λ := (CFSG.pPrimeCore q X).map X.subtype with hNdef
  have hNn : N.Normal := i1810_map_normal_of_characteristic _
  have hNX : N ≤ X := Subgroup.map_subtype_le _
  have hNq : Nat.Coprime q (Nat.card N) := by
    rw [hNdef, Subgroup.card_map_of_injective X.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  set π : Λ →* Λ ⧸ N := QuotientGroup.mk' N with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hcomap : ∀ H : Subgroup Λ, N ≤ H → (H.map π).comap π = H := by
    intro H hH
    rw [Subgroup.comap_map_eq, hker, sup_eq_left.2 hH]
  have hmapc : ∀ M' : Subgroup (Λ ⧸ N), (M'.comap π).map π = M' :=
    fun M' => Subgroup.map_comap_eq_self_of_surjective hπ M'
  have hmaptop : (⊤ : Subgroup Λ).map π = ⊤ := Subgroup.map_top_of_surjective π hπ
  have hVn' : (V.map π).Normal := hVn.map π hπ
  have hXn' : (X.map π).Normal := hXn.map π hπ
  have hcardX : Nat.card X = Nat.card N * Nat.card (X.map π) := by
    rw [← i1810_card_comap_mk N (X.map π)]
    exact congrArg (fun H : Subgroup Λ => Nat.card H) (hcomap X hNX).symm
  refine i1810S_false_reduced hSch (CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hΛ N) hp hq
    (V.map π) (Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd V π) hVp)
    (by rw [← hmaptop, ← Subgroup.map_commutator, hperf])
    (by
      intro M' hM' hidx
      have hM : (M'.comap π).Normal := hM'.comap π
      rw [← Subgroup.index_comap_of_surjective M' hπ] at hidx
      rw [← hmapc M', hpp _ hM hidx, hmaptop])
    (X.map π) (Subgroup.map_mono hXV)
    (by rw [← hmaptop, ← Subgroup.map_commutator, hXX])
    (Q.map π) (Subgroup.map_mono hQX) (hQq.map π)
    (by
      rw [← Subgroup.relIndex_comap]
      intro hdvd
      exact hQi (hdvd.trans (Subgroup.relIndex_dvd_of_le_left X (Subgroup.le_comap_map π Q))))
    (by
      intro N' hN' hN'X hN'q
      have hM : (N'.comap π).Normal := hN'.comap π
      have hle1 : N'.comap π ≤ X := by
        have h := Subgroup.comap_mono (f := π) hN'X
        rwa [hcomap X hNX] at h
      have hcop : Nat.Coprime q (Nat.card (N'.comap π)) := by
        rw [i1810_card_comap_mk N N']
        exact Nat.Coprime.mul_right hNq hN'q
      have hsub : (N'.comap π).subgroupOf X ≤ CFSG.pPrimeCore q X := by
        refine le_sSup ⟨hM.subgroupOf X, ?_⟩
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle1).toEquiv]
      have hle2 : N'.comap π ≤ N := by
        intro x hx
        exact ⟨⟨x, hle1 hx⟩, hsub hx, rfl⟩
      rw [eq_bot_iff, ← hmapc N']
      exact (Subgroup.map_mono hle2).trans (le_of_eq ((Subgroup.map_eq_bot_iff N).2 hker.ge)))
    (Nat.Coprime.dvd_of_dvd_mul_left hNq (hcardX ▸ hqX))
    (by
      have hC : (Subgroup.centralizer (Q : Set Λ)).map π ≤
          Subgroup.centralizer ((Q.map π : Subgroup (Λ ⧸ N)) : Set (Λ ⧸ N)) := by
        rintro _ ⟨c, hc, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨y, hy, rfl⟩
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hc y hy]
      rw [eq_top_iff, ← hmaptop, ← hCV, Subgroup.map_sup]
      exact sup_le_sup hC le_rfl)

theorem i1810S_centralizer_le (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hΛ : CFSG.Open.IsKGroup Λ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hperf : ⁅(⊤ : Subgroup Λ), (⊤ : Subgroup Λ)⁆ = ⊤)
    (hpp : ∀ M : Subgroup Λ, M.Normal → ¬ p ∣ M.index → M = ⊤)
    (X : Subgroup Λ) [hXn : X.Normal] (hXV : X ≤ GLAPPrimeCore p Λ)
    (hXX : ⁅X, (⊤ : Subgroup Λ)⁆ = X)
    (Q : Subgroup Λ) (hQX : Q ≤ X) (hQq : IsPGroup q Q) (hQi : ¬ q ∣ Q.relIndex X)
    (hqX : q ∣ Nat.card X)
    (hdich : Subgroup.centralizer (Q : Set Λ) ⊔ GLAPPrimeCore p Λ = ⊤ ∨
      ⁅Subgroup.centralizer (Q : Set Λ) ⊔ GLAPPrimeCore p Λ, (⊤ : Subgroup Λ)⁆ ≤
        GLAPPrimeCore p Λ) :
    Subgroup.centralizer (Q : Set Λ) ≤
      (CFSG.pCore p (Λ ⧸ GLAPPrimeCore p Λ)).comap (QuotientGroup.mk' (GLAPPrimeCore p Λ)) := by
  have : Fact p.Prime := ⟨hp⟩
  set V : Subgroup Λ := GLAPPrimeCore p Λ with hVdef
  set π : Λ →* Λ ⧸ V := QuotientGroup.mk' V with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective V
  have hker : π.ker = V := QuotientGroup.ker_mk' V
  have hVp : Nat.Coprime p (Nat.card V) := CFSG.pPrimeCore_coprime_card (p := p) (G := Λ)
  have hcomm : ∀ a b : Λ, ⁅a, b⁆ ∈ V ↔ π a * π b = π b * π a := by
    intro a b
    rw [← QuotientGroup.eq_one_iff]
    change π ⁅a, b⁆ = 1 ↔ _
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  have hmain : ⁅Subgroup.centralizer (Q : Set Λ) ⊔ V, (⊤ : Subgroup Λ)⁆ ≤ V := by
    rcases hdich with h | h
    · exact (i1810S_false hSch hΛ hp hq V hVp hperf hpp X hXV hXX Q hQX hQq hQi hqX h).elim
    · exact h
  have hpc : CFSG.pPrimeCore p (Λ ⧸ V) = ⊥ := by
    rw [CFSG.pPrimeCore_eq_bot_iff]
    intro K hK hKc
    have hle : K.comap π ≤ V :=
      le_sSup ⟨hK.comap π, by rw [i1810_card_comap_mk V K]; exact Nat.Coprime.mul_right hVp hKc⟩
    rw [eq_bot_iff, ← Subgroup.map_comap_eq_self_of_surjective hπ K]
    exact (Subgroup.map_mono hle).trans (le_of_eq ((Subgroup.map_eq_bot_iff V).2 hker.ge))
  have hZp : Subgroup.center (Λ ⧸ V) ≤ CFSG.pCore p (Λ ⧸ V) := by
    exact le_sSup ⟨inferInstance,
      CFSG.isPGroup_of_nilpotent_normal _ inferInstance inferInstance hpc⟩
  intro c hc
  rw [Subgroup.mem_comap]
  apply hZp
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨g, rfl⟩ := hπ y
  have h1 : ⁅c, g⁆ ∈ V :=
    hmain (Subgroup.commutator_mem_commutator (Subgroup.mem_sup_left hc) (Subgroup.mem_top g))
  exact ((hcomm c g).1 h1).symm

end Lambda

section Product

variable {G : Type} [Group G] [Finite G]

theorem i1810S_component_conj {p : ℕ} (hp : p.Prime) {Y K₁ B : Subgroup G}
    (hK₁ : GLAPComponent p Y K₁) (hBY : B ≤ Subgroup.normalizer (Y : Set G)) {b : G}
    (hb : b ∈ B) : GLAPComponent p (closureIn K₁ B) (GLBConj b K₁) := by
  have h1 : GLAPComponent p Y (GLBConj b K₁) := by
    have := glaPComponent_gLBConj hK₁ b
    rwa [mem_normalizer_iff_gLBConj_eq.1 (hBY hb)] at this
  have h2 : GLBConj b K₁ ≤ closureIn K₁ B := by
    rw [closureIn_eq_iSup_gLBConj K₁ B]
    exact le_biSup (fun g => GLBConj g K₁) hb
  exact glaPComponent_of_le hp h1 h2 (layer_closureIn hp hK₁ hBY).1

theorem i1810S_dichotomy {p : ℕ} (hp : p.Prime) {Y K₁ B M : Subgroup G}
    (hK₁ : GLAPComponent p Y K₁) (hBY : B ≤ Subgroup.normalizer (Y : Set G))
    (hMK : M ≤ closureIn K₁ B) [hMn : (M.subgroupOf (closureIn K₁ B)).Normal]
    (hBM : B ≤ Subgroup.normalizer (M : Set G)) :
    M = closureIn K₁ B ∨
      (⁅M, closureIn K₁ B⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p (closureIn K₁ B) := by
  set K := closureIn K₁ B
  have hconj : ∀ b ∈ B, GLAPComponent p K (GLBConj b K₁) := fun b hb =>
    i1810S_component_conj hp hK₁ hBY hb
  have hsup : K = ⨆ g ∈ B, GLBConj g K₁ := closureIn_eq_iSup_gLBConj K₁ B
  by_cases hex : ∃ b ∈ B, GLBConj b K₁ ≤ M
  · left
    obtain ⟨b₀, hb₀, hle⟩ := hex
    refine le_antisymm hMK ?_
    refine hsup.le.trans (iSup₂_le fun b hb => ?_)
    have hx : b₀⁻¹ * b ∈ B := B.mul_mem (B.inv_mem hb₀) hb
    have h1 : GLBConj (b₀⁻¹ * b) (GLBConj b₀ K₁) = GLBConj b K₁ := by
      rw [gLBConj_gLBConj, mul_inv_cancel_left]
    have h2 : GLBConj (b₀⁻¹ * b) M = M := mem_normalizer_iff_gLBConj_eq.1 (hBM hx)
    calc GLBConj b K₁ = GLBConj (b₀⁻¹ * b) (GLBConj b₀ K₁) := h1.symm
      _ ≤ GLBConj (b₀⁻¹ * b) M := CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono _ hle
      _ = M := h2
  · right
    push Not at hex
    set S : Subgroup (↥K ⧸ GLAPPrimeCore p ↥K) :=
      Subgroup.centralizer (barX p K M : Set (↥K ⧸ GLAPPrimeCore p ↥K)) with hS
    have hJS : ∀ b ∈ B, GLBConj b K₁ ≤
        (S.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥K))).map K.subtype := by
      intro b hb
      have hJK : GLBConj b K₁ ≤ K := (hconj b hb).1
      rw [← i183_barX_le_iff hJK, hS]
      rcases i183_le_or_commutator_eq_bot hp (hconj b hb) hMK with h | h
      · exact absurd h (hex b hb)
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    have hKS : K ≤ (S.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥K))).map K.subtype :=
      hsup.le.trans (iSup₂_le fun b hb => hJS b hb)
    rw [Subgroup.commutator_le]
    intro m hm k hk
    obtain ⟨k', hk'S, rfl⟩ := hKS hk
    have hmbar : QuotientGroup.mk' (GLAPPrimeCore p ↥K) (⟨m, hMK hm⟩ : ↥K) ∈ barX p K M :=
      ⟨⟨m, hMK hm⟩, Subgroup.mem_subgroupOf.2 hm, rfl⟩
    have hcomm : QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⁅(⟨m, hMK hm⟩ : ↥K), k'⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_comap.1 hk'S) _ hmbar
    exact ⟨⁅(⟨m, hMK hm⟩ : ↥K), k'⁆, (QuotientGroup.eq_one_iff _).1 hcomm, rfl⟩

private theorem le_normalizer_centralizer_of_le' {A R : Subgroup G}
    (h : A ≤ Subgroup.normalizer (R : Set G)) :
    A ≤ Subgroup.normalizer ((Subgroup.centralizer (R : Set G) : Subgroup G) : Set G) := by
  have key : ∀ b ∈ A, ∀ c ∈ Subgroup.centralizer (R : Set G),
      b * c * b⁻¹ ∈ Subgroup.centralizer (R : Set G) := by
    intro b hb c hc
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : b⁻¹ * r * b ∈ R := by
      have := (Subgroup.mem_normalizer_iff.1 (h (A.inv_mem hb)) r).1 hr
      simpa using this
    have hcr := Subgroup.mem_centralizer_iff.1 hc _ hr'
    calc r * (b * c * b⁻¹) = b * ((b⁻¹ * r * b) * c) * b⁻¹ := by group
      _ = b * (c * (b⁻¹ * r * b)) * b⁻¹ := by rw [hcr]
      _ = b * c * b⁻¹ * r := by group
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key a ha x
  · intro hx
    have := key a⁻¹ (A.inv_mem ha) _ hx
    simpa [mul_assoc] using this

theorem i1810UsedAt_of_schreier
    (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (G : Type) [Group G] [Finite G] (p : ℕ) : I1810UsedAt G p := by
  intro hp _ Y K₁ B R hY hK₁ _ hBY hR1 hR2 hRX hRidx hBR
  have hSch : CFSG.AGLEmbedding.KFactCatalogSchreier := hS
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKY, hBK, -, hlay⟩ := layer_closureIn hp hK₁ hBY
  obtain ⟨hXK, -, hKX, -, hXOK, -⟩ := commutator_oPrime_facts hp hK₁ hBY
  set K : Subgroup G := closureIn K₁ B
  set X : Subgroup G := (⁅K, GLAPPrimeCoreOf p Y⁆ : Subgroup G) with hXdef
  have hRK : R ≤ K := hRX.trans hXK
  have hΛ : CFSG.Open.IsKGroup ↥K :=
    hY.of_injective (Subgroup.inclusion hKY) (Subgroup.inclusion_injective hKY)
  have hperfK : (⁅K, K⁆ : Subgroup G) = K := by
    refine le_antisymm (commutator_self_le K) ?_
    calc K = GLAPLayer p K := hlay.symm
      _ ≤ ⁅K, K⁆ := sSup_le fun L hL =>
        (glaPComponent_perfect hL).symm.le.trans (Subgroup.commutator_mono hL.1 hL.1)
  have hperf : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hperfK]
  have hres : ∀ N : Subgroup G, N ≤ K → (N.subgroupOf K).Normal →
      Nat.Coprime p (N.subgroupOf K).index → N = K := by
    have h := layer_isOPrimeResidual hp K
    rw [hlay] at h
    exact h
  have hpp : ∀ M : Subgroup ↥K, M.Normal → ¬ p ∣ M.index → M = ⊤ := by
    intro M hM hidx
    have hsub : (M.map K.subtype).subgroupOf K = M :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective M
    have h := hres (M.map K.subtype) (Subgroup.map_subtype_le M) (by rw [hsub]; exact hM)
      (by rw [hsub]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hidx)
    rw [← hsub, h, Subgroup.subgroupOf_self]
  have hXXG : (⁅X, K⁆ : Subgroup G) = X := by
    have h := i321UsedAt_holds p hp (GLAPPrimeCoreOf p Y) K
      (i183_coprime_card_glaPPrimeCoreOf hp Y) (hKY.trans (le_normalizer_glaPPrimeCoreOf p Y)) hres
    rw [hXdef, Subgroup.commutator_comm K (GLAPPrimeCoreOf p Y)]
    exact h
  have hVsub : (GLAPPrimeCoreOf p K).subgroupOf K = GLAPPrimeCore p ↥K :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hVK : GLAPPrimeCoreOf p K ≤ K := Subgroup.map_subtype_le _
  have hXV : X.subgroupOf K ≤ GLAPPrimeCore p ↥K := by
    rw [← hVsub]
    exact Subgroup.comap_mono hXOK
  have hXXΛ : ⁅X.subgroupOf K, (⊤ : Subgroup ↥K)⁆ = X.subgroupOf K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hXK]
    exact hXXG
  haveI hXn : (X.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).2 hKX
  have hQq : IsPGroup 2 (R.subgroupOf K) := hR2.comap_of_injective K.subtype K.subtype_injective
  have hQX : R.subgroupOf K ≤ X.subgroupOf K := Subgroup.comap_mono hRX
  have hQi : ¬ 2 ∣ (R.subgroupOf K).relIndex (X.subgroupOf K) := by
    rw [Subgroup.relIndex_subgroupOf hXK]
    exact hRidx
  have hqX : 2 ∣ Nat.card (X.subgroupOf K) := by
    haveI : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).2 hR1
    obtain ⟨n, hn, hcard⟩ := hR2.nontrivial_iff_card.1 inferInstance
    have h1 : 2 ∣ Nat.card R := by
      rw [hcard]
      exact dvd_pow_self 2 hn.ne'
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv]
    exact h1.trans (Subgroup.card_dvd_of_le hRX)
  set C : Subgroup G := K ⊓ Subgroup.centralizer (R : Set G)
  set V : Subgroup G := GLAPPrimeCoreOf p K
  have hCsub : C.subgroupOf K = Subgroup.centralizer ((R.subgroupOf K : Subgroup ↥K) : Set ↥K) :=
    i183_subgroupOf_inf_centralizer hRK
  have hMsub : (C ⊔ V).subgroupOf K =
      Subgroup.centralizer ((R.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊔ GLAPPrimeCore p ↥K := by
    rw [Subgroup.subgroupOf_sup inf_le_left hVK, hCsub, hVsub]
  haveI hMn : ((C ⊔ V).subgroupOf K).Normal := by
    rw [hMsub]
    exact i1810S_centralizer_sup_normal (GLAPPrimeCore p ↥K) (X.subgroupOf K) (R.subgroupOf K)
      hXV hQX hQq hQi
  have hMK : C ⊔ V ≤ K := sup_le inf_le_left hVK
  have hBM : B ≤ Subgroup.normalizer ((C ⊔ V : Subgroup G) : Set G) :=
    le_normalizer_sup (le_normalizer_inf hBK (le_normalizer_centralizer_of_le' hBR))
      (hBK.trans (normalizer_le_normalizer_glaPPrimeCoreOf p K))
  have hdich := i1810S_dichotomy hp hK₁ hBY hMK hBM
  have hdichΛ : Subgroup.centralizer ((R.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊔
        GLAPPrimeCore p ↥K = ⊤ ∨
      ⁅Subgroup.centralizer ((R.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊔ GLAPPrimeCore p ↥K,
        (⊤ : Subgroup ↥K)⁆ ≤ GLAPPrimeCore p ↥K := by
    rcases hdich with h | h
    · left
      rw [← hMsub, h, Subgroup.subgroupOf_self]
    · right
      rw [← hMsub, Subgroup.commutator_le]
      intro a ha g _
      have ha' : (a : G) ∈ C ⊔ V := Subgroup.mem_subgroupOf.1 ha
      have h' : ⁅(a : G), (g : G)⁆ ∈ V := h (Subgroup.commutator_mem_commutator ha' g.2)
      rw [← hVsub]
      exact Subgroup.mem_subgroupOf.2 h'
  have hmain := i1810S_centralizer_le hSch hΛ hp Nat.prime_two hperf hpp (X.subgroupOf K) hXV
    hXXΛ (R.subgroupOf K) hQX hQq hQi hqX hdichΛ
  intro x hx
  have hxC : (⟨x, hx.1⟩ : ↥K) ∈
      Subgroup.centralizer ((R.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    rw [← hCsub]
    exact Subgroup.mem_subgroupOf.2 hx
  exact ⟨⟨x, hx.1⟩, hmain hxC, rfl⟩

end Product

end CFSG.LocalAnalysis.GLTheoremA
