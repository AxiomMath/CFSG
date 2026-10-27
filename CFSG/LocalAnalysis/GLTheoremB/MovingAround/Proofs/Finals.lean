module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop112
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped Pointwise

section Final

variable {G : Type} [Group G] [Finite G]

theorem exists_component_of_Iof_ne_bot {p : ℕ} {M D : Subgroup G} (h : Iof p M D ≠ ⊥) :
    ∃ L : Subgroup G, GLAPComponent p M L ∧
      ¬ barX p M (gammaStar p D) ≤ Subgroup.centralizer
        ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  by_contra hcon
  push Not at hcon
  apply h
  unfold Iof
  refine eq_bot_iff.2 (iSup₂_le fun L hL => ?_)
  exact False.elim (hL.2 (hcon L hL.1))

theorem barX_inf_self {p : ℕ} (C X : Subgroup G) : barX p C (X ⊓ C) = barX p C X := by
  unfold barX
  congr 1
  ext m
  simp [Subgroup.mem_subgroupOf, m.2]

theorem gammaStar_le_pCoreOf_piStar (p : ℕ) (D : Subgroup G) :
    gammaStar p D ≤ pCoreOf 2 (piStar p D) := by
  unfold gammaStar
  exact inf_le_right

theorem final_of_prop1310_of_lemma133 (h133 : Lemma133Statement) : Final_of_prop1310Statement := by
  intro G _ _ m p B M E A D T h hcov
  have hp : p.Prime := h.standing.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI : Iof p M D ≠ ⊥ := (h133 h).1
  obtain ⟨L, hL, hnc⟩ := exists_component_of_Iof_ne_bot hI
  have hcomp : IsComponentOf (barX p M L) ⊤ := by
    have hL' := hL
    obtain ⟨-, -, hc, -⟩ := hL'
    exact hc
  have hLI : L ≤ Istar p M D := by
    have h1 : L ≤ Iof p M D := by
      unfold Iof
      exact le_iSup₂_of_le L ⟨hL, hnc⟩ le_rfl
    have h2 : Iof p M D ≤ Istar p M D := by
      unfold Istar
      exact le_iSup₂_of_le (1 : G) M.one_mem (le_of_eq (gLBConj_one _).symm)
    exact h1.trans h2
  have hLpi : barX p M L ≤ barX p M (piStar p D) :=
    (barX_mono (p := p) (C := M) hLI).trans hcov
  have hU2 : IsPGroup 2 ↥(pCoreOf 2 (piStar p D) ⊓ M) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (piStar p D)).to_le inf_le_left
  have hS2 : IsPGroup 2 ↥(barX p M (pCoreOf 2 (piStar p D) ⊓ M)) := by
    unfold barX
    exact (hU2.of_equiv (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : pCoreOf 2 (piStar p D) ⊓ M ≤ M)).symm).map _
  have hnorm : piStar p D ⊓ M ≤
      Subgroup.normalizer ((pCoreOf 2 (piStar p D) ⊓ M : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_inf] at hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1
      (le_normalizer_pCoreOf 2 (piStar p D) hy.1) x
    have h2 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hy.2) x
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr h1 h2
  have hLbN : barX p M L ≤ Subgroup.normalizer
      ((barX p M (pCoreOf 2 (piStar p D) ⊓ M) : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
    have h := barX_le_normalizer (p := p) (C := M) hnorm
    rw [barX_inf_self (p := p) M (piStar p D)] at h
    exact hLpi.trans h
  have hcomm : ⁅barX p M L, barX p M (pCoreOf 2 (piStar p D) ⊓ M)⁆ = ⊥ :=
    commutator_eq_bot_of_normalizes hcomp hS2 hLbN
  have hcentr : barX p M (pCoreOf 2 (piStar p D) ⊓ M) ≤ Subgroup.centralizer
      ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
    rw [Subgroup.commutator_comm] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hΓ : barX p M (gammaStar p D) ≤ barX p M (pCoreOf 2 (piStar p D) ⊓ M) := by
    rw [← barX_inf_self (p := p) M (gammaStar p D)]
    exact barX_mono (p := p) (C := M)
      (inf_le_inf (gammaStar_le_pCoreOf_piStar p D) (le_refl M))
  exact hnc (hΓ.trans hcentr)

end Final

section Prop117

variable {G : Type} [Group G] [Finite G]

@[expose] def cexConjOn {S B : Subgroup G} (h : ∀ s ∈ S, ∀ b ∈ B, s * b * s⁻¹ ∈ B) :
    S →* MulAut B where
  toFun s :=
    { toFun := fun b => ⟨(s : G) * b * (s : G)⁻¹, h s s.2 b b.2⟩
      invFun := fun b => ⟨(s : G)⁻¹ * b * s, by
        have := h _ (S.inv_mem s.2) b b.2
        rwa [inv_inv] at this⟩
      left_inv := fun b => Subtype.ext (by dsimp only; group)
      right_inv := fun b => Subtype.ext (by dsimp only; group)
      map_mul' := fun b b' => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        group) }
  map_one' := MulEquiv.ext fun b => Subtype.ext (by
    show ((1 : S) : G) * b * ((1 : S) : G)⁻¹ = b
    rw [OneMemClass.coe_one, one_mul, inv_one, mul_one])
  map_mul' s s' := MulEquiv.ext fun b => Subtype.ext (by
    show ((s * s' : S) : G) * b * ((s * s' : S) : G)⁻¹ = s * (s' * b * (s' : G)⁻¹) * (s : G)⁻¹
    rw [Subgroup.coe_mul]
    group)

theorem cex117_le_normalizer_of_invariant {A R : Subgroup G}
    (hA : ∀ a ∈ A, ∀ r ∈ R, a * r * a⁻¹ ∈ R) : A ≤ Subgroup.normalizer (R : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hA a ha x
  · intro hx
    have := hA a⁻¹ (A.inv_mem ha) _ hx
    simpa [mul_assoc] using this

theorem exists_isMaxInvTwoSub_ge {H A R : Subgroup G} (hRH : R ≤ H) (hR2 : IsPGroup 2 ↥R)
    (hRA : A ≤ Subgroup.normalizer (R : Set G)) :
    ∃ T : Subgroup G, R ≤ T ∧ IsMaxInvTwoSub H A T := by
  classical
  obtain ⟨T, hTS, hTmax⟩ := Set.exists_max_image
    {T : Subgroup G | T ≤ H ∧ IsPGroup 2 ↥T ∧ A ≤ Subgroup.normalizer (T : Set G) ∧ R ≤ T}
    (fun T => Nat.card ↥T) (Set.toFinite _) ⟨R, hRH, hR2, hRA, le_rfl⟩
  refine ⟨T, hTS.2.2.2, hTS.1, hTS.2.1, hTS.2.2.1, fun T' hT'H hT'2 hT'A hTT' => ?_⟩
  have hmem : T' ∈ {T : Subgroup G | T ≤ H ∧ IsPGroup 2 ↥T ∧
      A ≤ Subgroup.normalizer (T : Set G) ∧ R ≤ T} :=
    ⟨hT'H, hT'2, hT'A, hTS.2.2.2.trans hTT'⟩
  have hc : Nat.card ↥T' ≤ Nat.card ↥T := hTmax T' hmem
  exact (Subgroup.eq_of_le_of_card_ge hTT' hc).symm

theorem isSylowIn_map_sylow {N : Subgroup G} (P : Sylow 2 ↥N) :
    IsSylowIn 2 N ((P : Subgroup ↥N).map N.subtype) := by
  refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map N.subtype, fun R' hR'N hR'2 hPR' => ?_⟩
  have hQ : IsPGroup 2 ↥(R'.subgroupOf N) :=
    hR'2.comap_of_injective N.subtype Subtype.val_injective
  have hPle : (P : Subgroup ↥N) ≤ R'.subgroupOf N := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hPR' (Subgroup.mem_map.2 ⟨x, hx, rfl⟩))
  have hEq : R'.subgroupOf N = (P : Subgroup ↥N) := P.is_maximal' hQ hPle
  refine le_antisymm (fun r hr => ?_) hPR'
  have hr' : (⟨r, hR'N hr⟩ : ↥N) ∈ R'.subgroupOf N := Subgroup.mem_subgroupOf.2 hr
  rw [hEq] at hr'
  exact Subgroup.mem_map.2 ⟨_, hr', rfl⟩

theorem exists_invariant_sylowIn_two {A N : Subgroup G} (hA : IsPGroup 3 ↥A)
    (hAN : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) (h3 : ¬ 3 ∣ Nat.card ↥N) :
    ∃ R : Subgroup G, IsSylowIn 2 N R ∧ ∀ a ∈ A, ∀ r ∈ R, a * r * a⁻¹ ∈ R := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : MulAction ↥A (Sylow 2 ↥N) := MulAction.compHom _ (cexConjOn hAN)
  have hndvd : ¬ 3 ∣ Nat.card (Sylow 2 ↥N) := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 ↥N) := inferInstance
    intro h
    exact h3 (h.trans ((Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card _)))
  obtain ⟨P₀, hP₀⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 ↥N) hndvd
  refine ⟨(P₀ : Subgroup ↥N).map N.subtype, isSylowIn_map_sylow P₀, ?_⟩
  intro a ha r hr
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hr
  have hfix : (⟨a, ha⟩ : ↥A) • P₀ = P₀ := hP₀ ⟨a, ha⟩
  have hmem : cexConjOn hAN ⟨a, ha⟩ y ∈ (((⟨a, ha⟩ : ↥A) • P₀ : Sylow 2 ↥N) : Subgroup ↥N) := by
    show cexConjOn hAN ⟨a, ha⟩ y ∈ cexConjOn hAN ⟨a, ha⟩ • (P₀ : Subgroup ↥N)
    exact Subgroup.smul_mem_pointwise_smul y _ _ hy
  rw [hfix] at hmem
  exact Subgroup.mem_map.2 ⟨_, hmem, rfl⟩

theorem prop117_cex_false_of_lemmas (h1111 : Lemma1111Statement) (h1114 : Lemma1114Statement)
    (h1115i : Lemma1115_iStatement) (h1115ii : Lemma1115_iiStatement)
    (h1115iii : Lemma1115_iiiStatement) : Prop117_cex_falseStatement := by
  intro G _ _ m p B M E A a K h
  obtain ⟨rfl, -, -⟩ := h1111 h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSC : IsSCp 3 M A := h.pair.1.2.1.1.1
  have hAM : A ≤ M := hSC.1
  have hA3 : IsPGroup 3 ↥A := hSC.2.1.isPGroup
  classical
  let PP : Set (Subgroup G × Subgroup G) :=
    {x | InHFamily A K a x.1 ∧ IsMaxInvTwoSub x.1 A x.2}
  have hne : PP.Nonempty := by
    obtain ⟨H₁, hH₁⟩ := h1115i h
    have hbot2 : IsPGroup 2 ↥(⊥ : Subgroup G) := fun g => ⟨0, by
      have : g = 1 := Subtype.ext (Subgroup.mem_bot.1 g.2)
      simp [this]⟩
    have hbotA : A ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
      intro a' _
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp
    obtain ⟨T₁, -, hT₁⟩ := exists_isMaxInvTwoSub_ge (H := H₁) (A := A) (R := ⊥) bot_le hbot2 hbotA
    exact ⟨(H₁, T₁), hH₁, hT₁⟩
  obtain ⟨⟨H, T⟩, ⟨hH, hT⟩, hmax⟩ :=
    Set.exists_max_image PP (fun x => Nat.card ↥x.2) (Set.toFinite _) hne
  have hH' : InHFamily A K a H := hH
  have hT' : IsMaxInvTwoSub H A T := hT
  obtain ⟨T0, -, hT0char, hH0⟩ := h1115ii h hH' hT'
  have hNH : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (T0 : Set G) :=
    hT0char.normalizer_le
  have hmaxH₀ : ∀ R : Subgroup G, R ≤ Subgroup.normalizer (T0 : Set G) → IsPGroup 2 ↥R →
      A ≤ Subgroup.normalizer (R : Set G) → T ≤ R → R = T := by
    intro R hRH hR2 hRA hTR
    obtain ⟨T', hRT', hT'max⟩ := exists_isMaxInvTwoSub_ge hRH hR2 hRA
    have hc : Nat.card ↥T' ≤ Nat.card ↥T := hmax (Subgroup.normalizer (T0 : Set G), T') ⟨hH0, hT'max⟩
    have hcR : Nat.card ↥R ≤ Nat.card ↥T := (Subgroup.card_le_of_le hRT').trans hc
    exact (Subgroup.eq_of_le_of_card_ge hTR hcR).symm
  have hTX : T ≤ GLAPPrimeCoreOf 3 M := by
    have hcop : Nat.Coprime 3 (Nat.card ↥T) := by
      obtain ⟨k, hk⟩ := hT.2.1.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k (by norm_num)
    exact (le_iSup₂_of_le (f := fun (T' : Subgroup G) (_ : IsInvThreePrimeSub ⊤ A T') => T') T
      ⟨le_top, hcop, hT.2.2.1⟩ le_rfl).trans (h1114 h)
  have hX3 : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCoreOf 3 M)) := sec11_glaPPrimeCoreOf_coprime M
  have hXM : GLAPPrimeCoreOf 3 M ≤ M := sec11_glaPPrimeCoreOf_le (p := 3) M
  have hNX : Subgroup.normalizer (T : Set G) ⊓ GLAPPrimeCoreOf 3 M ≤ GLAPPrimeCoreOf 3 M :=
    inf_le_right
  have hN3 : ¬ 3 ∣ Nat.card ↥(Subgroup.normalizer (T : Set G) ⊓ GLAPPrimeCoreOf 3 M) := by
    intro hd
    have h2 : 3 ∣ Nat.card ↥(GLAPPrimeCoreOf 3 M) := hd.trans (Subgroup.card_dvd_of_le hNX)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hX3 h2
  have hAN : ∀ a' ∈ A, ∀ n ∈ Subgroup.normalizer (T : Set G) ⊓ GLAPPrimeCoreOf 3 M,
      a' * n * a'⁻¹ ∈ Subgroup.normalizer (T : Set G) ⊓ GLAPPrimeCoreOf 3 M := by
    intro a' ha' n hn
    have ha'N : a' ∈ Subgroup.normalizer (T : Set G) := hT.2.2.1 ha'
    rw [Subgroup.mem_inf] at hn ⊢
    refine ⟨?_, ?_⟩
    · exact (Subgroup.normalizer (T : Set G)).mul_mem
        ((Subgroup.normalizer (T : Set G)).mul_mem ha'N hn.1)
        ((Subgroup.normalizer (T : Set G)).inv_mem ha'N)
    · exact sec11_glaPPrimeCoreOf_conj_mem (hAM ha') hn.2
  obtain ⟨R₀, hR₀N, hR₀A⟩ := exists_invariant_sylowIn_two hA3 hAN hN3
  have hR₀2 : IsPGroup 2 ↥R₀ := hR₀N.2.1
  have hR₀H : R₀ ≤ Subgroup.normalizer (T0 : Set G) :=
    hR₀N.1.trans ((inf_le_left : Subgroup.normalizer (T : Set G) ⊓ GLAPPrimeCoreOf 3 M ≤
      Subgroup.normalizer (T : Set G)).trans hNH)
  have hR₀T : R₀ ≤ Subgroup.normalizer (T : Set G) := hR₀N.1.trans inf_le_left
  have hTN : T ≤ Subgroup.normalizer (T : Set G) ⊓ GLAPPrimeCoreOf 3 M :=
    le_inf Subgroup.le_normalizer hTX
  have hTR₀ : T ≤ R₀ := by
    have hsup_le : T ⊔ R₀ ≤ Subgroup.normalizer (T : Set G) ⊓ GLAPPrimeCoreOf 3 M :=
      sup_le hTN hR₀N.1
    have hsup2 : IsPGroup 2 ↥(T ⊔ R₀) :=
      IsPGroup.to_sup_of_normal_left' hT.2.1 hR₀2 hR₀T
    have heq : T ⊔ R₀ = R₀ := hR₀N.2.2 (T ⊔ R₀) hsup_le hsup2 le_sup_right
    exact le_sup_left.trans heq.le
  have hTeqR₀ : R₀ = T :=
    hmaxH₀ R₀ hR₀H hR₀2 (cex117_le_normalizer_of_invariant hR₀A) hTR₀
  have hTsylowX : IsSylowIn 2 (GLAPPrimeCoreOf 3 M) T := by
    refine ⟨hTX, hT.2.1, fun S hSX hS2 hTS => ?_⟩
    have hle : S ⊓ Subgroup.normalizer (T : Set G) ≤
        Subgroup.normalizer (T : Set G) ⊓ GLAPPrimeCoreOf 3 M := fun s hs =>
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hs).2, hSX (Subgroup.mem_inf.1 hs).1⟩
    have hpg : IsPGroup 2 ↥(S ⊓ Subgroup.normalizer (T : Set G)) := hS2.to_le inf_le_left
    have hR₀le : R₀ ≤ S ⊓ Subgroup.normalizer (T : Set G) := by
      rw [hTeqR₀]
      exact le_inf hTS Subgroup.le_normalizer
    have key : S ⊓ Subgroup.normalizer (T : Set G) = R₀ :=
      hR₀N.2.2 _ hle hpg hR₀le
    exact (eq_of_normalizer_inf_eq hS2 hTS (key.trans hTeqR₀)).symm
  have hfrat : ∀ m' ∈ M, ∃ x ∈ GLAPPrimeCoreOf 3 M, ∃ n ∈ Subgroup.normalizer (T : Set G),
      m' = x * n := by
    intro m' hm'
    have hSX : GLBConj m'⁻¹ T ≤ GLAPPrimeCoreOf 3 M := by
      have h1 := gLBConj_mono m'⁻¹ hTX
      rw [gLBConj_eq_of_mem_normalizer
        (sec11_le_normalizer_glaPPrimeCoreOf (p := 3) M (M.inv_mem hm'))] at h1
      exact h1
    have hSp : IsPGroup 2 ↥(GLBConj m'⁻¹ T) := hT.2.1.map (MulAut.conj m'⁻¹⁻¹).toMonoidHom
    obtain ⟨c, hc, hcS⟩ := Lemma113b.exists_conj_mem_of_isSylowIn hTsylowX hSX hSp
    have hgT : ∀ k ∈ T, (c * m') * k * (c * m')⁻¹ ∈ T := by
      intro k hk
      have hmk : m' * k * m'⁻¹ ∈ GLBConj m'⁻¹ T := by
        rw [mem_gLBConj]
        simpa [mul_assoc] using hk
      have hck := hcS _ hmk
      have e : (c * m') * k * (c * m')⁻¹ = c * (m' * k * m'⁻¹) * c⁻¹ := by group
      rw [e]
      exact hck
    exact ⟨c⁻¹, (GLAPPrimeCoreOf 3 M).inv_mem hc, c * m', mem_normalizer_of_conj_le hgT,
      by group⟩
  have hcover : barX 3 M ⊤ ≤ barX 3 M (Subgroup.normalizer (T0 : Set G)) := by
    rintro z ⟨c, -, rfl⟩
    obtain ⟨x, hx, n, hn, hmxn⟩ := hfrat (c : G) c.2
    have hxM : x ∈ M := hXM hx
    have hnM : n ∈ M := by
      have h1 : n = x⁻¹ * (c : G) := by rw [hmxn]; group
      rw [h1]
      exact M.mul_mem (M.inv_mem hxM) c.2
    have hx1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨x, hxM⟩ : ↥M) = 1 :=
      (mem_glaPPrimeCoreOf_iff hxM).1 hx
    have hcn : c = (⟨x, hxM⟩ : ↥M) * ⟨n, hnM⟩ := Subtype.ext hmxn
    refine Subgroup.mem_map.2 ⟨⟨n, hnM⟩, Subgroup.mem_subgroupOf.2 (hNH hn), ?_⟩
    rw [hcn, map_mul, hx1, one_mul]
  exact h1115iii h hH0 hcover

end Prop117

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
