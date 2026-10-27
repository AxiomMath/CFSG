module

public import CFSG.HardMathSupport.Solomon.Coordinator.I18_10Action

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

theorem i1810_derivedSeries_eq_top {H : Type*} [Group H]
    (h : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = ⊤) (n : ℕ) : derivedSeries H n = ⊤ := by
  induction n with
  | zero => exact derivedSeries_zero H
  | succ n ih => rw [derivedSeries_succ, ih, h]

section Reduced

variable {Λ : Type} [Group Λ] [Finite Λ]

theorem i1810_reduced (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hΛ : CFSG.Open.IsKGroup Λ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (V : Subgroup Λ)
    [hVn : V.Normal] (hVp : Nat.Coprime p (Nat.card V))
    (hmin : ∀ M : Subgroup Λ, M.Normal → M ⊔ V = ⊤ → M = ⊤)
    (hperf : ⁅(⊤ : Subgroup Λ), (⊤ : Subgroup Λ)⁆ = ⊤)
    (hpp : ∀ M : Subgroup Λ, M.Normal → ¬ p ∣ M.index → M = ⊤)
    (hqs : ∀ M : Subgroup Λ, M.Normal → V ≤ M → M = ⊤ ∨ ⁅M, ⊤⁆ ≤ V)
    (Q : Subgroup Λ) (hQX : Q ≤ ⁅(⊤ : Subgroup Λ), V⁆) (hQq : IsPGroup q Q)
    (hQi : ¬ q ∣ Q.relIndex ⁅(⊤ : Subgroup Λ), V⁆)
    (hOq : ∀ N : Subgroup Λ, N.Normal → N ≤ ⁅(⊤ : Subgroup Λ), V⁆ →
      Nat.Coprime q (Nat.card N) → N = ⊥)
    (hqX : q ∣ Nat.card (⁅(⊤ : Subgroup Λ), V⁆ : Subgroup Λ)) :
    ⁅Subgroup.centralizer (Q : Set Λ) ⊔ V, ⊤⁆ ≤ V := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact p.Prime := ⟨hp⟩
  set X : Subgroup Λ := ⁅(⊤ : Subgroup Λ), V⁆ with hXdef
  set C : Subgroup Λ := Subgroup.centralizer (Q : Set Λ) with hCdef
  have hXn : X.Normal := Subgroup.commutator_normal ⊤ V
  have hXV : X ≤ V := Subgroup.commutator_le_right ⊤ V
  have hQX' : IsPGroup q (Q.subgroupOf X) :=
    hQq.of_equiv (Subgroup.subgroupOfEquivOfLe hQX).symm
  set QX : Sylow q X := hQX'.toSylow hQi with hQXdef
  have hQXmap : (QX : Subgroup X).map X.subtype = Q := by
    change (Q.subgroupOf X).map X.subtype = Q
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hQX]
  have hFr : Subgroup.normalizer (Q : Set Λ) ⊔ X = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top QX
    rwa [hQXmap] at h
  have hCVn : (C ⊔ V).Normal := by
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
  rcases hqs (C ⊔ V) hCVn le_sup_right with hCV | hCV
  swap
  · exact hCV
  exfalso
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
  have hX1 : X = ⊥ := by
    have h := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := ⊤) (H₂ := ⊤) (H₃ := V) hXc
      (by rw [Subgroup.commutator_comm V ⊤]; exact hXc)
    rwa [hperf] at h
  rw [hX1, Subgroup.card_bot] at hqX
  exact hq.one_lt.ne' (Nat.dvd_one.1 hqX)

theorem i1810_main (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hΛ : CFSG.Open.IsKGroup Λ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (V : Subgroup Λ)
    [hVn : V.Normal] (hVp : Nat.Coprime p (Nat.card V))
    (hmin : ∀ M : Subgroup Λ, M.Normal → M ⊔ V = ⊤ → M = ⊤)
    (hperf : ⁅(⊤ : Subgroup Λ), (⊤ : Subgroup Λ)⁆ = ⊤)
    (hpp : ∀ M : Subgroup Λ, M.Normal → ¬ p ∣ M.index → M = ⊤)
    (hqs : ∀ M : Subgroup Λ, M.Normal → V ≤ M → M = ⊤ ∨ ⁅M, ⊤⁆ ≤ V)
    (Q : Subgroup Λ) (hQX : Q ≤ ⁅(⊤ : Subgroup Λ), V⁆) (hQq : IsPGroup q Q)
    (hQi : ¬ q ∣ Q.relIndex ⁅(⊤ : Subgroup Λ), V⁆)
    (hqX : q ∣ Nat.card (⁅(⊤ : Subgroup Λ), V⁆ : Subgroup Λ)) :
    ⁅Subgroup.centralizer (Q : Set Λ) ⊔ V, ⊤⁆ ≤ V := by
  have : Fact q.Prime := ⟨hq⟩
  set X : Subgroup Λ := ⁅(⊤ : Subgroup Λ), V⁆ with hXdef
  have hXV : X ≤ V := Subgroup.commutator_le_right ⊤ V
  set N : Subgroup Λ := (CFSG.pPrimeCore q X).map X.subtype with hNdef
  have hNn : N.Normal := i1810_map_normal_of_characteristic _
  have hNX : N ≤ X := Subgroup.map_subtype_le _
  have hNV : N ≤ V := hNX.trans hXV
  have hNq : Nat.Coprime q (Nat.card N) := by
    rw [hNdef, Subgroup.card_map_of_injective X.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  set π : Λ →* Λ ⧸ N := QuotientGroup.mk' N with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hcomap : ∀ H : Subgroup Λ, N ≤ H → (H.map π).comap π = H := by
    intro H hH
    rw [Subgroup.comap_map_eq, hker, sup_eq_left.2 hH]
  have hNle : ∀ M' : Subgroup (Λ ⧸ N), N ≤ M'.comap π := fun M' =>
    hker.symm.le.trans (Subgroup.ker_le_comap π M')
  have hmapc : ∀ M' : Subgroup (Λ ⧸ N), (M'.comap π).map π = M' :=
    fun M' => Subgroup.map_comap_eq_self_of_surjective hπ M'
  have hmaptop : (⊤ : Subgroup Λ).map π = ⊤ := Subgroup.map_top_of_surjective π hπ
  set V' : Subgroup (Λ ⧸ N) := V.map π with hV'def
  have : V'.Normal := hVn.map π hπ
  have hX' : ⁅(⊤ : Subgroup (Λ ⧸ N)), V'⁆ = X.map π := by
    rw [hXdef, Subgroup.map_commutator, hmaptop]
  have hcardX : Nat.card X = Nat.card N * Nat.card (X.map π) := by
    rw [← i1810_card_comap_mk N (X.map π)]
    exact congrArg (fun H : Subgroup Λ => Nat.card H) (hcomap X hNX).symm
  have key := i1810_reduced hSch (CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hΛ N) hp hq
    V' (Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd V π) hVp)
    (by
      intro M' hM' hsup
      have hM : (M'.comap π).Normal := hM'.comap π
      have h1 : M'.comap π ⊔ V = ⊤ := by
        have h2 : (M'.comap π ⊔ V).map π = ⊤ := by
          rw [Subgroup.map_sup, hmapc, ← hV'def, hsup]
        rw [← hcomap _ ((hNle M').trans le_sup_left), h2, Subgroup.comap_top]
      rw [← hmapc M', hmin _ hM h1, hmaptop])
    (by rw [← hmaptop, ← Subgroup.map_commutator, hperf])
    (by
      intro M' hM' hidx
      have hM : (M'.comap π).Normal := hM'.comap π
      rw [← Subgroup.index_comap_of_surjective M' hπ] at hidx
      rw [← hmapc M', hpp _ hM hidx, hmaptop])
    (by
      intro M' hM' hVM'
      have hM : (M'.comap π).Normal := hM'.comap π
      have hVM : V ≤ M'.comap π := (Subgroup.le_comap_map π V).trans (Subgroup.comap_mono hVM')
      rcases hqs _ hM hVM with h | h
      · left
        rw [← hmapc M', h, hmaptop]
      · right
        have h2 := Subgroup.map_mono (f := π) h
        rwa [Subgroup.map_commutator, hmapc, hmaptop] at h2)
    (Q.map π) (by rw [hX']; exact Subgroup.map_mono hQX) (hQq.map π)
    (by
      rw [hX', ← Subgroup.relIndex_comap]
      intro hdvd
      exact hQi (hdvd.trans (Subgroup.relIndex_dvd_of_le_left X (Subgroup.le_comap_map π Q))))
    (by
      intro N' hN' hN'X hN'q
      have hM : (N'.comap π).Normal := hN'.comap π
      have hle1 : N'.comap π ≤ X := by
        have h := Subgroup.comap_mono (f := π) (hN'X.trans hX'.le)
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
    (by
      rw [hX']
      exact Nat.Coprime.dvd_of_dvd_mul_left hNq (hcardX ▸ hqX))
  have hC : (Subgroup.centralizer (Q : Set Λ)).map π ≤
      Subgroup.centralizer ((Q.map π : Subgroup (Λ ⧸ N)) : Set (Λ ⧸ N)) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hc y hy]
  have h1 : (⁅Subgroup.centralizer (Q : Set Λ) ⊔ V, (⊤ : Subgroup Λ)⁆ : Subgroup Λ).map π ≤
      V' := by
    rw [Subgroup.map_commutator, Subgroup.map_sup, hmaptop]
    exact (Subgroup.commutator_mono (sup_le_sup_right hC _) le_rfl).trans key
  have h2 := Subgroup.map_le_iff_le_comap.1 h1
  rwa [hV'def, hcomap V hNV] at h2

end Reduced

end CFSG.HardMathSupport.Solomon.Coordinator
