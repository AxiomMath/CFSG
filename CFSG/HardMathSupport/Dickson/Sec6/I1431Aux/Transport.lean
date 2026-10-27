module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Rank
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldBasic

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.ComponentClassification.OuterAutomorphisms

theorem isFieldAutPSLn_congr {n : ℕ} {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    {α : MulAut Y} (h : IsFieldAutPSLn n α) : IsFieldAutPSLn n (MulAut.congr e α) := by
  obtain ⟨F, hF, hfin, θ, σ, φ, γ, hφ, hθ⟩ := h
  have hc : (Subgroup.center Y').map e.symm.toMonoidHom = Subgroup.center Y :=
    Subgroup.map_center_eq e.symm
  let ε : (Y' ⧸ Subgroup.center Y') ≃* (Y ⧸ Subgroup.center Y) :=
    QuotientGroup.congr (Subgroup.center Y') (Subgroup.center Y) e.symm hc
  refine ⟨F, hF, hfin, ε.trans θ, σ, φ, γ, hφ, fun y' => ?_⟩
  have h1 : ε (QuotientGroup.mk y') = QuotientGroup.mk (e.symm y') :=
    QuotientGroup.congr_mk _ _ _ hc y'
  have h2 : ε (QuotientGroup.mk ((MulAut.congr e α) y')) = QuotientGroup.mk (α (e.symm y')) := by
    rw [QuotientGroup.congr_mk _ _ _ hc]
    simp [MulAut.congr_apply]
  show θ (ε (QuotientGroup.mk ((MulAut.congr e α) y'))) =
    (γ * φ * γ⁻¹) (θ (ε (QuotientGroup.mk y')))
  rw [h2, h1]
  exact hθ (e.symm y')

section Comp

variable {G : Type} [Group G] [Finite G]

theorem comp_eq_of_map_eq {K S : Subgroup G} {J₁ J₂ : Subgroup ↥K}
    (h₁ : GLAPComponent 3 (S.subgroupOf K) J₁) (h₂ : GLAPComponent 3 (S.subgroupOf K) J₂)
    (h : J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) =
      J₂.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K))) : J₁ = J₂ := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  set A : Subgroup ↥K := S.subgroupOf K with hA
  set ψ : ↥K →* barOf 3 K := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) with hψ
  have hker : Nat.Coprime 3 (Nat.card ↥(A ⊓ ψ.ker)) := coprime_ker_mk K A
  have hb₁ := lcEquiv_barX hp ψ A hker h₁.1
  have hb₂ := lcEquiv_barX hp ψ A hker h₂.1
  have hbar : barX 3 A J₁ = barX 3 A J₂ := by
    apply Subgroup.map_injective (lcEquiv hp ψ A hker).injective
    show (barX 3 A J₁).map (lcMonoidHom hp ψ A hker) = (barX 3 A J₂).map (lcMonoidHom hp ψ A hker)
    rw [hb₁, hb₂, h]
  exact glaPComponent_uniqueAux h₁ h₂ hbar

variable {I : Subgroup G}

abbrev jbar (J₁ : Subgroup ↥I) : Subgroup (barOf 3 I) :=
  J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥I))

theorem rho_map_le {J₁ : Subgroup ↥I} {a : G} (ha : a ∈ Subgroup.normalizer (I : Set G))
    (haJ : a ∈ Subgroup.normalizer ((J₁.map I.subtype : Subgroup G) : Set G))
    {y : barOf 3 I} (hy : y ∈ jbar J₁) : barAut 3 I ⟨a, ha⟩ y ∈ jbar J₁ := by
  obtain ⟨j, hj, rfl⟩ := hy
  rw [QuotientGroup.mk'_apply, barAut_mk]
  have h1 : a * (j : G) * a⁻¹ ∈ (J₁.map I.subtype : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.1 haJ _).1 ⟨j, hj, rfl⟩
  obtain ⟨j', hj', hjj'⟩ := h1
  have h2 : I.normalizerMonoidHom ⟨a, ha⟩ j = j' := by
    apply Subtype.ext
    rw [normalizerMonoidHom_coe]
    exact hjj'.symm
  exact ⟨j', hj', by rw [QuotientGroup.mk'_apply, h2]⟩

theorem rho_mem_stab {J₁ : Subgroup ↥I} {a : G} (ha : a ∈ Subgroup.normalizer (I : Set G))
    (haJ : a ∈ Subgroup.normalizer ((J₁.map I.subtype : Subgroup G) : Set G)) :
    barAut 3 I ⟨a, ha⟩ ∈ stabAut (jbar J₁) := by
  intro y
  constructor
  · intro hy
    have ha' : a⁻¹ ∈ Subgroup.normalizer (I : Set G) := inv_mem ha
    have haJ' : a⁻¹ ∈ Subgroup.normalizer ((J₁.map I.subtype : Subgroup G) : Set G) := inv_mem haJ
    have h := rho_map_le ha' haJ' hy
    have hmul : (⟨a⁻¹, ha'⟩ : ↥(Subgroup.normalizer (I : Set G))) * ⟨a, ha⟩ = 1 :=
      Subtype.ext (inv_mul_cancel a)
    have h2 : barAut 3 I ⟨a⁻¹, ha'⟩ (barAut 3 I ⟨a, ha⟩ y) = y := by
      rw [← MulAut.mul_apply, ← map_mul, hmul, map_one, MulAut.one_apply]
    rwa [h2] at h
  · exact fun hy => rho_map_le ha haJ hy

theorem liftEquiv_barAut {J₁ : Subgroup ↥I} {a : G} (ha : a ∈ Subgroup.normalizer (I : Set G))
    (haJ : a ∈ Subgroup.normalizer ((J₁.map I.subtype : Subgroup G) : Set G)) :
    inducedBarHom (jbar J₁) ⟨barAut 3 I ⟨a, ha⟩, rho_mem_stab ha haJ⟩ =
      MulAut.congr (liftEquiv J₁) (barAut 3 (J₁.map I.subtype) ⟨a, haJ⟩) := by
  apply MulEquiv.ext
  intro z
  obtain ⟨w, rfl⟩ := (liftEquiv J₁).surjective z
  change _ = (liftEquiv J₁) (barAut 3 (J₁.map I.subtype) ⟨a, haJ⟩
    ((liftEquiv J₁).symm ((liftEquiv J₁) w)))
  rw [MulEquiv.symm_apply_apply]
  have key : ∀ (j : ↥I) (hj : j ∈ J₁),
      inducedBarHom (jbar J₁) ⟨barAut 3 I ⟨a, ha⟩, rho_mem_stab ha haJ⟩
        (liftEquiv J₁ (QuotientGroup.mk ⟨(j : G), ⟨j, hj, rfl⟩⟩)) =
      liftEquiv J₁ (barAut 3 (J₁.map I.subtype) ⟨a, haJ⟩
        (QuotientGroup.mk ⟨(j : G), ⟨j, hj, rfl⟩⟩)) := by
    intro j hj
    obtain ⟨j', hj', hjj'⟩ := (Subgroup.mem_normalizer_iff.1 haJ _).1 (⟨j, hj, rfl⟩ :
      (j : G) ∈ (J₁.map I.subtype : Subgroup G))
    have h2 : I.normalizerMonoidHom ⟨a, ha⟩ j = j' := by
      apply Subtype.ext
      rw [normalizerMonoidHom_coe]
      exact hjj'.symm
    have h3 : barAut 3 I ⟨a, ha⟩ (QuotientGroup.mk' (GLAPPrimeCore 3 ↥I) j) =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥I) j' := by
      rw [QuotientGroup.mk'_apply, barAut_mk, h2]
      rfl
    have h4 : barAut 3 (J₁.map I.subtype) ⟨a, haJ⟩ (QuotientGroup.mk ⟨(j : G), ⟨j, hj, rfl⟩⟩) =
        QuotientGroup.mk ⟨(j' : G), ⟨j', hj', rfl⟩⟩ := by
      rw [barAut_mk]
      congr 1
      apply Subtype.ext
      rw [normalizerMonoidHom_coe]
      exact hjj'.symm
    rw [liftEquiv_apply J₁ j hj, h4, liftEquiv_apply J₁ j' hj', inducedBarHom_mk]
    congr 1
    apply Subtype.ext
    exact h3
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨j, hj, hjx⟩ := x.2
  have hx : x = ⟨(j : G), ⟨j, hj, rfl⟩⟩ := Subtype.ext hjx.symm
  rw [hx]
  exact key j hj

theorem barAut_eq_one_of_rho_eq_one {J : Subgroup G} (hJI : J ≤ I) {a : G}
    (ha : a ∈ Subgroup.normalizer (I : Set G)) (haJ : a ∈ Subgroup.normalizer (J : Set G))
    (h1 : barAut 3 I ⟨a, ha⟩ = 1) : barAut 3 J ⟨a, haJ⟩ = 1 := by
  apply MulEquiv.ext
  intro z
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective z
  rw [MulAut.one_apply, barAut_mk, QuotientGroup.eq]
  have hjI : (j : G) ∈ I := hJI j.2
  have h2 := congrArg (fun φ : MulAut (barOf 3 I) => φ (QuotientGroup.mk ⟨(j : G), hjI⟩)) h1
  simp only [MulAut.one_apply] at h2
  rw [barAut_mk, QuotientGroup.eq, mem_GLAPPrimeCore_iff] at h2
  rw [mem_GLAPPrimeCore_iff]
  have h3 : GLAPPrimeCoreOf 3 I ⊓ J ≤ GLAPPrimeCoreOf 3 J := by
    have := gLAPPrimeCoreOf_inf_le Nat.prime_three I J
    rwa [inf_eq_right.2 hJI] at this
  refine h3 ⟨h2, SetLike.coe_mem _⟩

end Comp

section Ahat

variable {G : Type} [Group G] [Finite G] {I : Subgroup G}

@[expose] noncomputable def ahat (I A : Subgroup G) (hAN : A ≤ Subgroup.normalizer (I : Set G)) :
    Subgroup (MulAut (barOf 3 I)) :=
  ((barAut 3 I).comp (Subgroup.inclusion hAN)).range

theorem mem_ahat {A : Subgroup G} {hAN : A ≤ Subgroup.normalizer (I : Set G)}
    {e : MulAut (barOf 3 I)} :
    e ∈ ahat I A hAN ↔
      ∃ a ∈ A, ∃ ha : a ∈ Subgroup.normalizer (I : Set G), barAut 3 I ⟨a, ha⟩ = e := by
  constructor
  · rintro ⟨⟨a, haA⟩, rfl⟩
    exact ⟨a, haA, hAN haA, rfl⟩
  · rintro ⟨a, haA, ha, rfl⟩
    exact ⟨⟨a, haA⟩, rfl⟩

theorem rho_comp_injective {A B : Subgroup G} {x : G} {J : Subgroup G} (hJI : J ≤ I)
    (hB : B ≤ Subgroup.normalizer (I : Set G)) (hAB : A ≤ B) (hE : IsElemAbelian 3 B)
    (hx : x ∈ A) (hT : ¬ TrivOn I x)
    (hfld : ∀ a ∈ A, a ∉ Subgroup.zpowers x → InducesFieldAutN 2 J a ∧ ¬ TrivOn J a) :
    Function.Injective ((barAut 3 I).comp (Subgroup.inclusion (hAB.trans hB))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  rw [Subgroup.mem_bot]
  have hxN : x ∈ Subgroup.normalizer (I : Set G) := hB (hAB hx)
  have hx3 : x ^ 3 = 1 := hE.2 x (hAB hx)
  have haN : (a : G) ∈ Subgroup.normalizer (I : Set G) := hB (hAB a.2)
  have ha1 : barAut 3 I ⟨(a : G), haN⟩ = 1 := ha
  by_cases hax : (a : G) ∈ Subgroup.zpowers x
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hax
    have hρ3 : barAut 3 I ⟨x, hxN⟩ ^ 3 = 1 := Lemma510Ns.barAut_pow_three hxN hx3
    have hρ1 : barAut 3 I ⟨x, hxN⟩ ≠ 1 := fun h => hT ⟨hxN, h⟩
    have hord : orderOf (barAut 3 I ⟨x, hxN⟩) = 3 := orderOf_eq_prime hρ3 hρ1
    have hpow : (barAut 3 I ⟨x, hxN⟩) ^ k = 1 := by
      rw [← map_zpow]
      have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (I : Set G))) ^ k = ⟨(a : G), haN⟩ :=
        Subtype.ext (by simpa using hk)
      rw [this]
      exact ha1
    have hdvd : (3 : ℤ) ∣ k := by
      have := orderOf_dvd_iff_zpow_eq_one.2 hpow
      rw [hord] at this
      exact_mod_cast this
    obtain ⟨m, rfl⟩ := hdvd
    have : (a : G) = 1 := by
      rw [← hk, zpow_mul]
      have : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
      rw [this, one_zpow]
    exact Subtype.ext this
  · exfalso
    obtain ⟨⟨haJ, -⟩, hnt⟩ := hfld (a : G) a.2 hax
    exact hnt ⟨haJ, barAut_eq_one_of_rho_eq_one hJI haN haJ ha1⟩

theorem isElemAbelian_ahat {A : Subgroup G} {hAN : A ≤ Subgroup.normalizer (I : Set G)}
    (hA : IsElemAbelian 3 A) : IsElemAbelian 3 (ahat I A hAN) := by
  haveI := hA.1
  refine ⟨⟨⟨fun e₁ e₂ => ?_⟩⟩, fun e he => ?_⟩
  · obtain ⟨a₁, ha₁, h₁, he₁⟩ := mem_ahat.1 e₁.2
    obtain ⟨a₂, ha₂, h₂, he₂⟩ := mem_ahat.1 e₂.2
    apply Subtype.ext
    show (e₁ : MulAut (barOf 3 I)) * e₂ = e₂ * e₁
    rw [← he₁, ← he₂, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show a₁ * a₂ = a₂ * a₁
    have : (⟨a₁, ha₁⟩ : ↥A) * ⟨a₂, ha₂⟩ = ⟨a₂, ha₂⟩ * ⟨a₁, ha₁⟩ := mul_comm' _ _
    exact congrArg Subtype.val this
  · obtain ⟨a, haA, ha, rfl⟩ := mem_ahat.1 he
    rw [← map_pow]
    have : (⟨a, ha⟩ : ↥(Subgroup.normalizer (I : Set G))) ^ 3 = 1 := Subtype.ext (hA.2 a haA)
    rw [this, map_one]

theorem cfg_of_ambient (V : InndiagVocab) {B A : Subgroup G} {x : G} {J₁ : Subgroup ↥I} {q : ℕ}
    (hI : CFSG.Open.IsQuasisimple (barOf 3 I)) (hK : IsKGroup ↥I)
    (hB : B ≤ Subgroup.normalizer (I : Set G)) (hrk : GLATwoLocalRank 3 ↥(I ⊔ B) ≤ 4)
    (hE : IsElemAbelian 3 B) (hc : ∃ c ∈ B, c ≠ 1 ∧ c ∈ CD I) (hAB : A ≤ B) (hx : x ∈ A)
    (hA : Nat.card A = 9) (hT : ¬ TrivOn I x)
    (hJ₁ : GLAPComponent 3 ((I ⊓ Cs x).subgroupOf I) J₁)
    (hq : IsTypeL2 q (barOf 3 (J₁.map I.subtype))) (hq3 : ¬ 3 ∣ q) (hq8 : q ≠ 8)
    (hA' : ∀ a ∈ A, IndInn V I a)
    (hfld : ∀ a ∈ A, a ∉ Subgroup.zpowers x →
      InducesFieldAutN 2 (J₁.map I.subtype) a ∧ ¬ TrivOn (J₁.map I.subtype) a) :
    Y1431Cfg V (barOf 3 I) (ahat I A (hAB.trans hB)) (barAut 3 I ⟨x, hB (hAB hx)⟩)
      (jbar J₁) q := by
  have hxN : x ∈ Subgroup.normalizer (I : Set G) := hB (hAB hx)
  have hx3 : x ^ 3 = 1 := hE.2 x (hAB hx)
  have hJI : J₁.map I.subtype ≤ I := by
    rintro _ ⟨j, -, rfl⟩
    exact j.2
  obtain ⟨c, hcB, hc1, hcI⟩ := hc
  have hinj := rho_comp_injective (I := I) hJI hB hAB hE hx hT hfld
  refine ⟨hI, CFSG.IsKGroup.quotient hK _,
    CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCore_quotient_eq_bot Nat.prime_three,
    rkY_of_ambient hrk hE hcB hc1 hcI, isElemAbelian_ahat (c25_isElemAbelian_mono hAB hE), ?_,
    mem_ahat.2 ⟨x, hx, hxN, rfl⟩, fun h => hT ⟨hxN, h⟩, comp_map_fixSub hxN hx3 hJ₁,
    l2fld_isTypeL2_of_mulEquiv (liftEquiv J₁) hq, hq3, hq8, ?_, ?_⟩
  · rw [ahat, ← hA]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  · intro e he
    obtain ⟨a, haA, haN, rfl⟩ := mem_ahat.1 he
    obtain ⟨h, hmem⟩ := hA' a haA
    exact hmem
  · intro η hη hηξ
    obtain ⟨a, haA, haN, rfl⟩ := mem_ahat.1 hη
    have hax : a ∉ Subgroup.zpowers x := by
      intro hax
      apply hηξ
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hax
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      rw [← map_zpow]
      congr 1
      exact Subtype.ext (by simpa using hk)
    obtain ⟨⟨haJ, hfa⟩, hnt⟩ := hfld a haA hax
    refine ⟨⟨rho_mem_stab haN haJ, ?_⟩, ?_⟩
    · rw [liftEquiv_barAut haN haJ]
      exact isFieldAutPSLn_congr (liftEquiv J₁) hfa
    · rintro ⟨h, h1⟩
      apply hnt
      refine ⟨haJ, ?_⟩
      rw [liftEquiv_barAut haN haJ] at h1
      apply (MulAut.congr (liftEquiv J₁)).injective
      rw [h1, map_one]

section Back

variable {G : Type} [Group G] [Finite G] {I : Subgroup G}

theorem mem_cs_subgroupOf_iff (a : G) (y : ↥I) :
    y ∈ (I ⊓ Cs a).subgroupOf I ↔ a * (y : G) = (y : G) * a := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.2.symm, fun h => ⟨y.2, h.symm⟩⟩

theorem mem_cs_iff_conj {a b : G} (hbN : b ∈ Subgroup.normalizer (I : Set G))
    (hab : a * b = b * a) (y : ↥I) :
    y ∈ (I ⊓ Cs a).subgroupOf I ↔
      (I.normalizerMonoidHom ⟨b, hbN⟩ y) ∈ (I ⊓ Cs a).subgroupOf I := by
  rw [mem_cs_subgroupOf_iff, mem_cs_subgroupOf_iff, normalizerMonoidHom_coe]
  have hba : b * a * b⁻¹ = a := by rw [← hab]; group
  show a * (y : G) = (y : G) * a ↔ a * (b * (y : G) * b⁻¹) = (b * (y : G) * b⁻¹) * a
  constructor
  · intro h
    have h1 := congrArg (fun t => b * t * b⁻¹) h
    calc a * (b * (y : G) * b⁻¹) = (b * a * b⁻¹) * (b * (y : G) * b⁻¹) := by rw [hba]
      _ = b * (a * (y : G)) * b⁻¹ := by group
      _ = b * ((y : G) * a) * b⁻¹ := h1
      _ = (b * (y : G) * b⁻¹) * (b * a * b⁻¹) := by group
      _ = (b * (y : G) * b⁻¹) * a := by rw [hba]
  · intro h
    have h' : b * (a * (y : G)) * b⁻¹ = b * ((y : G) * a) * b⁻¹ := by
      calc b * (a * (y : G)) * b⁻¹ = (b * a * b⁻¹) * (b * (y : G) * b⁻¹) := by group
        _ = a * (b * (y : G) * b⁻¹) := by rw [hba]
        _ = (b * (y : G) * b⁻¹) * a := h
        _ = (b * (y : G) * b⁻¹) * (b * a * b⁻¹) := by rw [hba]
        _ = b * ((y : G) * a) * b⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h')

theorem map_cs_subgroupOf {a b : G} (hbN : b ∈ Subgroup.normalizer (I : Set G))
    (hab : a * b = b * a) :
    ((I ⊓ Cs a).subgroupOf I).map (I.normalizerMonoidHom ⟨b, hbN⟩).toMonoidHom =
      (I ⊓ Cs a).subgroupOf I := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_cs_iff_conj hbN hab x).1 hx
  · intro hy
    refine ⟨(I.normalizerMonoidHom ⟨b, hbN⟩).symm y, ?_, by simp⟩
    have := (mem_cs_iff_conj hbN hab ((I.normalizerMonoidHom ⟨b, hbN⟩).symm y)).2
    simp only [MulEquiv.apply_symm_apply] at this
    exact this hy

theorem comp_map_conj {a b : G} (hbN : b ∈ Subgroup.normalizer (I : Set G))
    (hab : a * b = b * a) {K₁ : Subgroup ↥I}
    (hK : GLAPComponent 3 ((I ⊓ Cs a).subgroupOf I) K₁) :
    GLAPComponent 3 ((I ⊓ Cs a).subgroupOf I)
      (K₁.map (I.normalizerMonoidHom ⟨b, hbN⟩).toMonoidHom) := by
  have hker : Nat.Coprime 3 (Nat.card ↥(((I ⊓ Cs a).subgroupOf I) ⊓
      (I.normalizerMonoidHom ⟨b, hbN⟩).toMonoidHom.ker)) := by
    have hkerbot : (I.normalizerMonoidHom ⟨b, hbN⟩).toMonoidHom.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff (I.normalizerMonoidHom ⟨b, hbN⟩).toMonoidHom).2
        (I.normalizerMonoidHom ⟨b, hbN⟩).injective
    rw [hkerbot, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right _
  have := glaPComponent_map Nat.prime_three (I.normalizerMonoidHom ⟨b, hbN⟩).toMonoidHom hker hK
  rwa [map_cs_subgroupOf hbN hab] at this

theorem jbar_map_conj {b : G} (hbN : b ∈ Subgroup.normalizer (I : Set G)) (K₁ : Subgroup ↥I) :
    jbar (K₁.map (I.normalizerMonoidHom ⟨b, hbN⟩).toMonoidHom) =
      (jbar K₁).map (barAut 3 I ⟨b, hbN⟩).toMonoidHom := by
  unfold jbar
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem conj_map_subtype {b : G} (hbN : b ∈ Subgroup.normalizer (I : Set G)) (K₁ : Subgroup ↥I) :
    (K₁.map (I.normalizerMonoidHom ⟨b, hbN⟩).toMonoidHom).map I.subtype =
      GLBConj b⁻¹ (K₁.map I.subtype) := by
  ext z
  rw [mem_gLBConj]
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨k, hk, ?_⟩
    show (k : G) = b⁻¹ * ((I.normalizerMonoidHom ⟨b, hbN⟩ k : ↥I) : G) * b⁻¹⁻¹
    rw [normalizerMonoidHom_coe]
    group
  · rintro ⟨k, hk, hkz⟩
    refine ⟨I.normalizerMonoidHom ⟨b, hbN⟩ k, ⟨k, hk, rfl⟩, ?_⟩
    show ((I.normalizerMonoidHom ⟨b, hbN⟩ k : ↥I) : G) = z
    rw [normalizerMonoidHom_coe]
    have : (k : G) = b⁻¹ * z * b⁻¹⁻¹ := hkz
    rw [this]
    group

theorem ambient_of_concl {B A : Subgroup G} {x : G} {J₁ : Subgroup ↥I} {q : ℕ}
    (hB : B ≤ Subgroup.normalizer (I : Set G)) (hE : IsElemAbelian 3 B) (hAB : A ≤ B)
    (hx : x ∈ A) (hJ₁ : GLAPComponent 3 ((I ⊓ Cs x).subgroupOf I) J₁)
    (hconcl : Y1431Concl (barOf 3 I) (ahat I A (hAB.trans hB))
      (barAut 3 I ⟨x, hB (hAB hx)⟩) (jbar J₁) q) :
    (∃ r0 : ℕ, r0 ^ 3 = q ∧ IsPSUn 6 r0 (barOf 3 I ⧸ Subgroup.center (barOf 3 I))) ∧
    J₁.map I.subtype = CLay I x ∧
    ∃ a ∈ A, a ≠ 1 ∧ ∃ r0 : ℕ, r0 ^ 3 = q ∧ ∃ H₁ H₂ H₃ : Subgroup G,
      GLAPComponent 3 (I ⊓ Cs a) H₁ ∧ GLAPComponent 3 (I ⊓ Cs a) H₂ ∧
      GLAPComponent 3 (I ⊓ Cs a) H₃ ∧ H₁ ≠ H₂ ∧ H₁ ≠ H₃ ∧ H₂ ≠ H₃ ∧
      CLay I a = H₁ ⊔ H₂ ⊔ H₃ ∧
      (∀ H : Subgroup G, (H = H₁ ∨ H = H₂ ∨ H = H₃) → IsTypeL2 r0 (barOf 3 H)) ∧
      ∀ H H' : Subgroup G, (H = H₁ ∨ H = H₂ ∨ H = H₃) → (H' = H₁ ∨ H' = H₂ ∨ H' = H₃) →
        ∃ e ∈ A, GLBConj e H = H' := by
  have hxN : x ∈ Subgroup.normalizer (I : Set G) := hB (hAB hx)
  have hx3 : x ^ 3 = 1 := hE.2 x (hAB hx)
  refine ⟨hconcl.psu, ?_, ?_⟩
  ·
    show J₁.map I.subtype = GLAPLayer 3 (I ⊓ Cs x)
    apply le_antisymm
    · exact le_sSup (comp_map_subgroupOf inf_le_left hJ₁)
    · refine sSup_le fun L hL => ?_
      obtain ⟨L₂, hL₂, rfl⟩ := exists_comp_subgroupOf inf_le_left hL
      have himg := hconcl.layer (jbar L₂) (comp_map_fixSub hxN hx3 hL₂)
      have : L₂ = J₁ := comp_eq_of_map_eq hL₂ hJ₁ himg
      rw [this]
  ·
    obtain ⟨η, hηA, hη1, r0, hr0, Ĥ₁, Ĥ₂, Ĥ₃, hcomp, h12, h13, h23, hty, htrans⟩ := hconcl.triple
    obtain ⟨a, haA, haN, rfl⟩ := mem_ahat.1 hηA
    have ha3 : a ^ 3 = 1 := hE.2 a (hAB haA)
    have hne1 : a ≠ 1 := by
      rintro rfl
      apply hη1
      have : (⟨1, haN⟩ : ↥(Subgroup.normalizer (I : Set G))) = 1 := rfl
      rw [this, map_one]
    refine ⟨a, haA, hne1, r0, hr0, ?_⟩
    obtain ⟨K₁, hK₁, hK₁m⟩ := exists_comp_of_fixSub haN ha3 ((hcomp Ĥ₁).2 (Or.inl rfl))
    obtain ⟨K₂, hK₂, hK₂m⟩ := exists_comp_of_fixSub haN ha3 ((hcomp Ĥ₂).2 (Or.inr (Or.inl rfl)))
    obtain ⟨K₃, hK₃, hK₃m⟩ := exists_comp_of_fixSub haN ha3 ((hcomp Ĥ₃).2 (Or.inr (Or.inr rfl)))
    subst hK₁m hK₂m hK₃m
    have hsel : ∀ H : Subgroup G,
        (H = K₁.map I.subtype ∨ H = K₂.map I.subtype ∨ H = K₃.map I.subtype) →
        ∃ Ki : Subgroup ↥I, GLAPComponent 3 ((I ⊓ Cs a).subgroupOf I) Ki ∧
          H = Ki.map I.subtype ∧ (jbar Ki = jbar K₁ ∨ jbar Ki = jbar K₂ ∨ jbar Ki = jbar K₃) := by
      rintro H (rfl | rfl | rfl)
      · exact ⟨K₁, hK₁, rfl, Or.inl rfl⟩
      · exact ⟨K₂, hK₂, rfl, Or.inr (Or.inl rfl)⟩
      · exact ⟨K₃, hK₃, rfl, Or.inr (Or.inr rfl)⟩
    have hne : ∀ {Ki Kj : Subgroup ↥I}, jbar Ki ≠ jbar Kj → Ki.map I.subtype ≠ Kj.map I.subtype := by
      intro Ki Kj h hK
      apply h
      rw [Subgroup.map_injective I.subtype_injective hK]
    have key : ∀ (Ki Kj : Subgroup ↥I), GLAPComponent 3 ((I ⊓ Cs a).subgroupOf I) Ki →
        GLAPComponent 3 ((I ⊓ Cs a).subgroupOf I) Kj →
        (∃ e ∈ ahat I A (hAB.trans hB), (jbar Ki).map e.toMonoidHom = jbar Kj) →
        ∃ e ∈ A, GLBConj e (Ki.map I.subtype) = Kj.map I.subtype := by
      rintro Ki Kj hKi hKj ⟨e, heA, he⟩
      obtain ⟨b, hbA, hbN, rfl⟩ := mem_ahat.1 heA
      refine ⟨b⁻¹, inv_mem hbA, ?_⟩
      haveI := hE.1
      have hab : a * b = b * a := congrArg Subtype.val
        (mul_comm' (⟨a, hAB haA⟩ : ↥B) ⟨b, hAB hbA⟩)
      have hconj := comp_map_conj hbN hab hKi
      have himg : jbar (Ki.map (I.normalizerMonoidHom ⟨b, hbN⟩).toMonoidHom) = jbar Kj := by
        rw [jbar_map_conj hbN, he]
      have hKK := comp_eq_of_map_eq hconj hKj himg
      rw [← conj_map_subtype hbN Ki, hKK]
    refine ⟨K₁.map I.subtype, K₂.map I.subtype, K₃.map I.subtype,
      comp_map_subgroupOf inf_le_left hK₁, comp_map_subgroupOf inf_le_left hK₂,
      comp_map_subgroupOf inf_le_left hK₃, hne h12, hne h13, hne h23, ?_, ?_, ?_⟩
    · show GLAPLayer 3 (I ⊓ Cs a) = _
      apply le_antisymm
      · refine sSup_le fun L hL => ?_
        obtain ⟨L₂, hL₂, rfl⟩ := exists_comp_subgroupOf inf_le_left hL
        rcases (hcomp (jbar L₂)).1 (comp_map_fixSub haN ha3 hL₂) with h | h | h
        · rw [comp_eq_of_map_eq hL₂ hK₁ h]
          exact le_sup_of_le_left le_sup_left
        · rw [comp_eq_of_map_eq hL₂ hK₂ h]
          exact le_sup_of_le_left le_sup_right
        · rw [comp_eq_of_map_eq hL₂ hK₃ h]
          exact le_sup_right
      · exact sup_le (sup_le (le_sSup (comp_map_subgroupOf inf_le_left hK₁))
          (le_sSup (comp_map_subgroupOf inf_le_left hK₂)))
          (le_sSup (comp_map_subgroupOf inf_le_left hK₃))
    · intro H hH
      obtain ⟨Ki, hKi, rfl, hi⟩ := hsel H hH
      exact l2fld_isTypeL2_of_mulEquiv (liftEquiv Ki).symm (hty (jbar Ki) hi)
    · intro H H' hH hH'
      obtain ⟨Ki, hKi, rfl, hi⟩ := hsel H hH
      obtain ⟨Kj, hKj, rfl, hj⟩ := hsel H' hH'
      exact key Ki Kj hKi hKj (htrans _ _ hi hj)

end Back

end Ahat

theorem input14_31_4_of_Y {V : InndiagVocab} (h : Y1431 V) : Input14_31_4 V := by
  intro G _ _ I B hI hK hB hrk hE hc A x hAB hx hA hT J hJ q hq hq3 hq8 hA' hfld
  obtain ⟨J₁, hJ₁, rfl⟩ := exists_comp_subgroupOf (inf_le_left : I ⊓ Cs x ≤ I) hJ
  exact ambient_of_concl hB hE hAB hx hJ₁
    (h _ _ _ _ _ (cfg_of_ambient V hI hK hB hrk hE hc hAB hx hA hT hJ₁ hq hq3 hq8 hA' hfld))

end CFSG.HardMathSupport.Dickson.Sec6.I1431
