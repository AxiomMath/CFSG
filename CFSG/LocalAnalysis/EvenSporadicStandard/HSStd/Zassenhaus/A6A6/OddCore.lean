module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Prod
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Layer
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Gl8
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResChiefAbs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.M24Std CFSG.EvenSporadicStandard.M23Std

theorem not_dvd_card_mulAut {W : Type} [Group W] [Finite W] (hc : ∀ a b : W, a * b = b * a)
    {p r : ℕ} (hp : p.Prime) (hr : p ^ r ∣ 9838563) (hr1 : 1 ≤ r) (hexp : ∀ w : W, w ^ p = 1)
    (hcard : Nat.card W = p ^ r) : ¬ 360 ∣ Nat.card (MulAut W) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := p) hc hexp hcard
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  have hpd : p ∣ 3 * 7 * 7 * 17 * 31 * 127 :=
    (dvd_pow_self p (by omega)).trans hr
  have hp5 : p = 3 ∨ p = 7 ∨ p = 17 ∨ p = 31 ∨ p = 127 := by
    rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
          · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
            · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)
            · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h))
          · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h))
        · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h))))
  have hr2 : r ≤ 2 := by
    by_contra h
    have h3 : p ^ 3 ∣ 9838563 := (pow_dvd_pow p (by omega)).trans hr
    rcases hp5 with rfl | rfl | rfl | rfl | rfl <;> norm_num at h3
  rcases hp5 with rfl | rfl | rfl | rfl | rfl <;> interval_cases r <;>
    first
    | (exfalso; norm_num at hr; done)
    | simp [Fin.prod_univ_succ]

theorem forall_eq_one_of_alt6 {X W : Type} [Group X] [Group W] [Finite W]
    (e : X ≃* alternatingGroup (Fin 6)) (φ : X →* MulAut W) (h : ¬ 360 ∣ Nat.card (MulAut W)) :
    ∀ x, φ x = 1 := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 6))
  have : IsSimpleGroup X := e.isSimpleGroup
  rcases (φ.normal_ker).eq_bot_or_eq_top with hk | hk
  · exfalso
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hk
    apply h
    have := Subgroup.card_dvd_of_injective φ hinj
    rwa [Nat.card_congr e.toEquiv, card_alternatingGroup_six] at this
  · intro x
    have : x ∈ φ.ker := by rw [hk]; exact mem_top x
    exact this

theorem comm_of_alt6 {G : Type} [Group G] [Finite G] {M : Subgroup G} [M.Normal] {X : Subgroup G}
    (e : X ≃* alternatingGroup (Fin 6)) (h : ¬ 360 ∣ Nat.card (MulAut (chiefW ⊥ M))) :
    ∀ x ∈ X, ∀ m ∈ M, x * m = m * x := by
  intro x hx m hm
  have h1 := forall_eq_one_of_alt6 e ((chiefAct ⊥ M).comp X.subtype) h ⟨x, hx⟩
  have hw : QuotientGroup.mk' (⊥ : Subgroup G) m ∈ chiefW ⊥ M := ⟨m, hm, rfl⟩
  have h2 := chiefAct_apply (⊥ : Subgroup G) M x ⟨_, hw⟩
  have h3 : chiefAct ⊥ M x ⟨_, hw⟩ = ⟨_, hw⟩ := by
    have := congrArg (fun f : MulAut (chiefW ⊥ M) => f ⟨_, hw⟩) h1
    simpa using this
  rw [h3] at h2
  have hinj : Function.Injective (QuotientGroup.mk' (⊥ : Subgroup G)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
  have h4 : QuotientGroup.mk' (⊥ : Subgroup G) m =
      QuotientGroup.mk' (⊥ : Subgroup G) (x * m * x⁻¹) := by
    rw [map_mul, map_mul, map_inv]
    exact h2
  have h5 := hinj h4
  calc x * m = (x * m * x⁻¹) * x := by group
    _ = m * x := by rw [← h5]

theorem Config.fusionOddCore_eq_bot_of_cent {V : Type} [Group V] (hc : ∀ x y : V, x * y = y * x)
    (hs : ∀ x : V, x * x = 1) (hV : Nat.card V = 256) {G : Type} [Group G] [Finite G]
    {ρ : G →* MulAut V} (hρ : Function.Injective ρ) (c : Config ρ)
    (hcent : ∀ g : MulAut V, (∀ x ∈ c.C ⊔ c.D, g * ρ x = ρ x * g) → g = 1) :
    fusionOddCore G = ⊥ := by
  classical
  by_contra hne
  have hFT : OddSolv := fun _ _ _ h => CFSG.FeitThompson.isSolvable_of_odd_natCard _ h
  have hNodd : Odd (Nat.card (fusionOddCore G)) := natCard_fusionOddCore_odd G
  obtain ⟨M, ⟨hMn, hMN, hMne⟩, hmin⟩ := WellFounded.has_min
    (wellFounded_lt (α := Subgroup G))
    {K : Subgroup G | K.Normal ∧ K ≤ fusionOddCore G ∧ K ≠ ⊥} ⟨fusionOddCore G, inferInstance,
      le_rfl, hne⟩
  have := hMn
  have hModd : Odd (Nat.card M) := Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le hMN)
  have hchief : ∀ K : Subgroup G, K.Normal → ⊥ ≤ K → K ≤ M → K = ⊥ ∨ K = M := by
    intro K hK _ hKM
    by_cases hK0 : K = ⊥
    · exact Or.inl hK0
    · right
      have := hmin K ⟨hK, hKM.trans hMN, hK0⟩
      exact (lt_or_eq_of_le hKM).resolve_left this
  obtain ⟨p, r, hp, hp2, hcardW, hexp, hcommW⟩ :=
    chief_elemAb hFT (bot_le : (⊥ : Subgroup G) ≤ M) (Ne.symm hMne) hModd hchief
  have hinj : Function.Injective (QuotientGroup.mk' (⊥ : Subgroup G)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
  have hcardM : Nat.card M = p ^ r := by
    rw [← hcardW, chiefW, Subgroup.card_map_of_injective hinj]
  have hMCD : M ⊓ (c.C ⊔ c.D) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have := c.inf_odd
    have hx' : x ∈ (c.C ⊔ c.D) ⊓ fusionOddCore G := ⟨hx.2, hMN hx.1⟩
    rw [c.inf_odd] at hx'
    exact hx'
  have hdvd1 : Nat.card ↥(c.C ⊔ c.D) ∣ Nat.card (G ⧸ M) := by
    refine Subgroup.card_dvd_of_injective ((QuotientGroup.mk' M).comp (c.C ⊔ c.D).subtype) ?_
    rw [← MonoidHom.ker_eq_bot_iff]
    refine eq_bot_iff.2 fun x hx => ?_
    have hx1 : (x : G) ∈ M := (QuotientGroup.eq_one_iff _).1 hx
    have : (x : G) ∈ M ⊓ (c.C ⊔ c.D) := ⟨hx1, x.2⟩
    rw [hMCD] at this
    exact Subtype.ext ((Subgroup.mem_bot).1 this)
  have hdvd2 : Nat.card G = Nat.card (G ⧸ M) * Nat.card M :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup M
  have hgl := M22Std.card_dvd_gl8 hc hs hV ρ hρ
  have hdiv : 129600 * p ^ r ∣ 129600 * (2 ^ 22 * 9838563) := by
    have h1 : 129600 * p ^ r ∣ Nat.card G := by
      rw [c.card_sup] at hdvd1
      rw [← hcardM, hdvd2]
      exact Nat.mul_dvd_mul hdvd1 dvd_rfl
    refine h1.trans (hgl.trans ?_)
    unfold M22Std.gl8
    norm_num
  have hdiv2 : p ^ r ∣ 2 ^ 22 * 9838563 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdiv
  have hcop : Nat.Coprime (p ^ r) (2 ^ 22) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hdiv3 : p ^ r ∣ 9838563 := hcop.dvd_of_dvd_mul_left hdiv2
  have hr1 : 1 ≤ r := by
    by_contra h0
    have hr0 : r = 0 := by omega
    rw [hr0, pow_zero] at hcardM
    exact hMne (Subgroup.card_eq_one.1 hcardM)
  have : Finite (chiefW ⊥ M) := inferInstance
  have hno : ¬ 360 ∣ Nat.card (MulAut (chiefW ⊥ M)) :=
    not_dvd_card_mulAut hcommW hp hdiv3 hr1 hexp hcardW
  have hCc := comm_of_alt6 (M := M) c.eC hno
  have hDc := comm_of_alt6 (M := M) c.eD hno
  have hle : c.C ⊔ c.D ≤ centralizer (M : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [mem_centralizer_iff]
      intro m hm
      exact (hCc x hx m hm).symm
    · rw [mem_centralizer_iff]
      intro m hm
      exact (hDc x hx m hm).symm
  apply hMne
  refine eq_bot_iff.2 fun m hm => ?_
  have h1 : ρ m = 1 := by
    apply hcent
    intro x hx
    have := mem_centralizer_iff.1 (hle hx) m hm
    rw [← map_mul, ← map_mul, this]
  rw [Subgroup.mem_bot]
  exact hρ (by rw [h1, map_one])

theorem isComponentOf_top_of_alt6 {G : Type} [Group G] {H K : Subgroup G} [K.Normal] (hHK : H ≤ K)
    (hn : K ≤ normalizer (H : Set G)) (e : H ≃* alternatingGroup (Fin 6)) :
    IsComponentOf H ⊤ := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 6))
  have : IsSimpleGroup H := e.isSimpleGroup
  have hnab : ∃ a b : H, a * b ≠ b * a := by
    let a : alternatingGroup (Fin 6) :=
      ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩
    let b : alternatingGroup (Fin 6) :=
      ⟨Equiv.swap 0 1 * Equiv.swap 0 3, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩
    refine ⟨e.symm a, e.symm b, fun h => ?_⟩
    have := congrArg e h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
    revert this
    decide
  obtain ⟨hq, -⟩ := M24Std.isQuasisimple_center_eq_bot_of_isSimpleGroup hnab
  refine ⟨le_top, ?_, hq⟩
  refine CFSG.Open.IsSubnormal.step hHK ?_
    (CFSG.Open.IsSubnormal.step le_top inferInstance (CFSG.Open.IsSubnormal.refl _))
  exact (normal_subgroupOf_iff_le_normalizer hHK).2 hn

theorem Config.egaLayer_eq {V : Type} [Group V] {G : Type} [Group G] [Finite G]
    {ρ : G →* MulAut V} (c : Config ρ) (hN : fusionOddCore G = ⊥) :
    egaLayer G = c.C ⊔ c.D := by
  have hker : (QuotientGroup.mk' (fusionOddCore G)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk', hN]
  have hK : c.C ⊔ c.D = (egaLayer (G ⧸ fusionOddCore G)).comap
      (QuotientGroup.mk' (fusionOddCore G)) := by
    rw [← c.map_eq, Subgroup.comap_map_eq, hker, sup_bot_eq]
  have : (c.C ⊔ c.D).Normal := by
    rw [hK]
    have := M24Std.egaLayer_normal (G ⧸ fusionOddCore G)
    infer_instance
  have hCn : c.C ⊔ c.D ≤ normalizer (c.C : Set G) := by
    refine sup_le le_normalizer ?_
    intro y hy
    refine centralizer_le_normalizer c.C ?_
    rw [mem_centralizer_iff]
    intro x hx
    exact c.comm x hx y hy
  have hDn : c.C ⊔ c.D ≤ normalizer (c.D : Set G) := by
    refine sup_le ?_ le_normalizer
    intro y hy
    refine centralizer_le_normalizer c.D ?_
    rw [mem_centralizer_iff]
    intro x hx
    exact (c.comm y hy x hx).symm
  have hCc := isComponentOf_top_of_alt6 (le_sup_left : c.C ≤ c.C ⊔ c.D) hCn c.eC
  have hDc := isComponentOf_top_of_alt6 (le_sup_right : c.D ≤ c.C ⊔ c.D) hDn c.eD
  apply le_antisymm
  · unfold egaLayer
    refine iSup_le fun K => iSup_le fun hKc => ?_
    have h1 : K.map (QuotientGroup.mk' (fusionOddCore G)) ≤
        egaLayer (G ⧸ fusionOddCore G) :=
      (Subgroup.map_mono (le_iSup₂_of_le (f := fun K (_ : IsComponentOf K ⊤) => K) K hKc
        le_rfl)).trans (M22Std.map_egaLayer_le _ (QuotientGroup.mk'_surjective _))
    rw [Subgroup.map_le_iff_le_comap, ← hK] at h1
    exact h1
  · exact sup_le (le_iSup₂_of_le (f := fun K (_ : IsComponentOf K ⊤) => K) c.C hCc le_rfl)
      (le_iSup₂_of_le (f := fun K (_ : IsComponentOf K ⊤) => K) c.D hDc le_rfl)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
