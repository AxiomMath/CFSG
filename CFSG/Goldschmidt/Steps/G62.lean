module

public import CFSG.Goldschmidt.StatementsG2
import CFSG.Goldschmidt.Steps.G62Basic
import CFSG.Walter.Bender1970.S3.PGroupFStar
public import CFSG.Goldschmidt.StatementsG

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.Walter
open CFSG.GorensteinWalter hiding oddCoreOf

namespace G62

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem normalizer_zj_eq_and_maximal (h311 : S_G311) (hset : GoldSetting G S A) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {M : Subgroup G} (hM : IsCoatom M)
    (hCM : Subgroup.centralizer (A : Set G) ≤ M)
    (hF : IsPGroup p (generalizedFittingSubgroupOf M)) {P : Subgroup G}
    (hP : Maximal (· ∈ sigN M A p) P) (hP1 : P ≠ ⊥) :
    Subgroup.normalizer (CFSG.Glauberman.ZJ P : Set G) = M ∧ Maximal (· ∈ sigN ⊤ A p) P := by
  have := hset.isSimpleGroup
  have : Fact p.Prime := ⟨hp⟩
  have hAM : A ≤ M := (le_centralizer hset).trans hCM
  have hMN := h311 G M A (isSStarIn_of_le hset hM.1 hAM) p hp hp2 P hP hF
  have hPp : IsPGroup p P := hP.1.2.1
  have hPM : P ≤ M := hP.1.1
  have hNZ : Subgroup.normalizer (CFSG.Glauberman.ZJ P : Set G) = M :=
    normalizer_eq_of_le_normalizer hM ((zj_le P).trans hPM) (zj_ne_bot hPp hP1) hMN
  refine ⟨hNZ, ?_⟩
  have hCtop : Subgroup.centralizer (A : Set G) ≤ ⊤ := le_top
  refine maximal_sigN_of_forall ((mem_sigN_iff_of_le hCM hCtop hPM le_top).mp hP.1) ?_
  intro Q hQ hPQ hQN
  have hQM : Q ≤ M := hQN.trans ((normalizer_le_normalizer_zj P).trans hNZ.le)
  exact hP.2 ((mem_sigN_iff_of_le hCM hCtop hQM le_top).mpr hQ) hPQ

theorem isPGroup_fstar_of_commutator_ne_bot (h51 : S_G51) (h37 : S_G37)
    (hset : GoldSetting G S A) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G}
    (hH : H ∈ benderM a) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : IsPGroup p (generalizedFittingSubgroupOf H)) {M : Subgroup G} (hM : IsCoatom M)
    (hCM : Subgroup.centralizer (A : Set G) ≤ M)
    (hX : ⁅fstarZero H ⊓ M, Subgroup.zpowers a⁆ ≠ ⊥) :
    IsPGroup p (generalizedFittingSubgroupOf M) := by
  have := hset.isSimpleGroup
  have : Fact p.Prime := ⟨hp⟩
  have ha2 : orderOf a = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (hset.elem.2 a haA) ha1
  have hHco := isCoatom_of_mem_benderM hH
  have haH : a ∈ H := mem_of_mem_benderM hH
  have hCaH := centralizer_le_of_mem_benderM hH
  have hH1 : H ≠ ⊥ := fun h => ha1 (Subgroup.mem_bot.mp (h ▸ haH))
  have hAM : A ≤ M := (le_centralizer hset).trans hCM
  have haM : a ∈ M := hAM haA
  have hMA := isSStarIn_of_le hset hM.1 hAM
  set X' := fstarZero H ⊓ M with hX'def
  have hX'p : IsPGroup p X' := hF.to_le (inf_le_left.trans (fstarZero_le H))
  have hCX' : M ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X' : Set G) :=
    fun c hc => CFSG.Walter.mem_normalizer_inf (le_normalizer_fstarZero H (hCaH hc.2))
      (Subgroup.le_normalizer hc.1)
  obtain ⟨⟨hXF, hXsub⟩, -⟩ := h37 G M A hMA hset.elem a haA ha1 X' inf_le_right hCX'
    (eq_componentLayerOf_sup_of_isPGroup hp hX'p (odd_card_of_isPGroup hp hp2 hX'p))
  set X := ⁅X', Subgroup.zpowers a⁆ with hXdef
  have haX' : a ∈ Subgroup.normalizer (X' : Set G) :=
    CFSG.Walter.mem_normalizer_inf (le_normalizer_fstarZero H haH) (Subgroup.le_normalizer haM)
  have hXX' : X ≤ X' := commutator_zpowers_le_of_mem_normalizer haX'
  have hXP₀ : X ≤ fstarZero H := hXX'.trans inf_le_left
  have hXp : IsPGroup p X := hX'p.to_le hXX'
  have hXO : X ≤ qCoreOf M p :=
    (le_qCoreOf_of_isSubnormal_isPGroup _ X p hXF hXsub hXp).trans
      (qCoreOf_le_qCoreOf_of_isNormalIn _ M p (generalizedFittingSubgroupOf_isNormalIn M))
  have hFF : CFSG.fittingSubgroupOf H ≤ generalizedFittingSubgroupOf H := le_sup_left
  have hU : UniquenessA a H := (h51 G S A hset a haA ha1 H hH).resolve_right fun h =>
    not_mem_of_isPGroup hp hp2 hF ha2 (hFF (qCoreOf_le_fittingSubgroupOf H 2 Nat.prime_two h.1))
  have hXA : X ∈ goldA a H := hU X hX hXP₀
    (isSubnormal_of_nilpotent (hF.to_le (fstarZero_le H)).isNilpotent X hXP₀)
    (CFSG.Walter.mem_normalizer_commutator haX'
      (Subgroup.le_normalizer (Subgroup.mem_zpowers a)))
  have hNX := isPGroup_fstar_normalizer_of_mem_goldA hHco hH1 hp hF hXA
  set PM := qCoreOf M p with hPMdef
  set Y := PM ⊓ Subgroup.normalizer (X : Set G) with hYdef
  have hXY : X ≤ Y := le_inf hXO Subgroup.le_normalizer
  have hYp : IsPGroup p Y := (qCoreOf_isPGroup M p).to_le inf_le_left
  have hCY : IsPGroup p (generalizedFittingSubgroupOf (Subgroup.centralizer (Y : Set G))) := by
    have h := isPGroup_generalizedFitting_inf_centralizer hp hNX inf_le_right hYp
    have hle : Subgroup.centralizer (Y : Set G) ≤ Subgroup.normalizer (X : Set G) :=
      (Subgroup.centralizer_le hXY).trans (Subgroup.centralizer_le_normalizer _)
    rwa [inf_eq_right.mpr hle] at h
  set Z := (Subgroup.center PM).map PM.subtype with hZdef
  have hZn : IsNormalIn Z M :=
    map_characteristic_isNormalIn_of_isNormalIn _ inferInstance (qCoreOf_normal_in M p)
  have hPM1 : PM ≠ ⊥ := fun h => hX (le_bot_iff.mp (h ▸ hXO))
  have hZ1 : Z ≠ ⊥ := by
    have : Nontrivial PM := (Subgroup.nontrivial_iff_ne_bot PM).mpr hPM1
    have := (qCoreOf_isPGroup M p).center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center PM)
    intro h
    have hzZ : ((z : PM) : G) ∈ Z := ⟨z, z.2, rfl⟩
    rw [h, Subgroup.mem_bot] at hzZ
    exact hz (Subtype.ext (Subtype.ext hzZ))
  have hZY : Z ≤ Y := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z.2, Subgroup.centralizer_le_normalizer _ ?_⟩
    show (z : G) ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨w, hXO hw⟩)
  have hNZ : Subgroup.normalizer (Z : Set G) = M :=
    normalizer_eq_of_le_normalizer hM hZn.1 hZ1 (le_normalizer_of_isNormalIn hZn)
  have hCYM : Subgroup.centralizer (Y : Set G) ≤ M :=
    (Subgroup.centralizer_le hZY).trans ((Subgroup.centralizer_le_normalizer _).trans hNZ.le)
  exact isPGroup_generalizedFitting_of_le_qCoreOf hp inf_le_left hCYM hCY

theorem eq_of_commutator_ne_bot (h311 : S_G311) (h51 : S_G51) (h37 : S_G37)
    (hset : GoldSetting G S A) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G}
    (hH : H ∈ benderM a) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : IsPGroup p (generalizedFittingSubgroupOf H)) {M₀ : Subgroup G} (hM₀ : IsCoatom M₀)
    (hCM₀ : Subgroup.centralizer (A : Set G) ≤ M₀)
    (hX₀ : ⁅fstarZero H ⊓ M₀, Subgroup.zpowers a⁆ ≠ ⊥) : M₀ = H := by
  have := hset.isSimpleGroup
  have : Fact p.Prime := ⟨hp⟩
  have hHco := isCoatom_of_mem_benderM hH
  have hCH : Subgroup.centralizer (A : Set G) ≤ H :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA)).trans
      (centralizer_le_of_mem_benderM hH)
  by_contra hM₀H
  set 𝒮 : Set (Subgroup G) := {M | IsCoatom M ∧ Subgroup.centralizer (A : Set G) ≤ M ∧
    ⁅fstarZero H ⊓ M, Subgroup.zpowers a⁆ ≠ ⊥ ∧ M ≠ H} with h𝒮
  obtain ⟨M, ⟨hMco, hCM, hXM, hMH⟩, hmax⟩ := Set.exists_max_image 𝒮
    (fun M => Nat.card (M ⊓ H : Subgroup G)) (Set.toFinite 𝒮) ⟨M₀, hM₀, hCM₀, hX₀, hM₀H⟩
  have hFM := isPGroup_fstar_of_commutator_ne_bot h51 h37 hset haA ha1 hH hp hp2 hF hMco hCM hXM
  set L := M ⊓ H with hLdef
  have hP₀H : fstarZero H ≤ H := (fstarZero_le H).trans (generalizedFittingSubgroupOf_le H)
  have hstep : ∀ K : Subgroup G, K ≠ ⊥ → K ≤ H → L ≤ Subgroup.normalizer (K : Set G) →
      H ⊓ Subgroup.normalizer (K : Set G) ≤ M ∨ M ⊓ Subgroup.normalizer (K : Set G) ≤ H := by
    intro K hK1 hKH hLK
    by_contra hc
    rw [not_or] at hc
    obtain ⟨x, hx, hxM⟩ := IsConcreteLE.not_le_iff_exists.mp hc.1
    obtain ⟨y, hy, hyH⟩ := IsConcreteLE.not_le_iff_exists.mp hc.2
    obtain ⟨M', hM'co, hNM'⟩ :=
      (eq_top_or_exists_le_coatom (Subgroup.normalizer (K : Set G))).resolve_left
        (normalizer_ne_top hK1 hKH hHco.1)
    have hLM' : L ≤ M' := hLK.trans hNM'
    have hCM' : Subgroup.centralizer (A : Set G) ≤ M' := (le_inf hCM hCH).trans hLM'
    have hM'H : M' ≠ H := fun h => hyH (h ▸ hNM' hy.2)
    have hXM' : ⁅fstarZero H ⊓ M', Subgroup.zpowers a⁆ ≠ ⊥ := by
      intro h
      apply hXM
      refine le_bot_iff.mp ((Subgroup.commutator_mono ?_ le_rfl).trans h.le)
      exact le_inf inf_le_left fun z hz => hLM' ⟨hz.2, hP₀H hz.1⟩
    have hlt : L < M' ⊓ H := by
      refine lt_of_le_of_ne (le_inf hLM' inf_le_right) fun h => hxM ?_
      have hxL : x ∈ L := by
        rw [h]
        exact ⟨hNM' hx.2, hx.1⟩
      exact hxL.1
    exact absurd (Subgroup.card_lt_of_lt hlt) (not_lt.mpr (hmax M' ⟨hM'co, hCM', hXM', hM'H⟩))
  set K' := fstarZero H ⊓ M with hK'def
  have hK'1 : K' ≠ ⊥ := fun h => hXM (by rw [h, Subgroup.commutator_bot_left])
  have hK'H : K' ≤ H := inf_le_left.trans hP₀H
  have hLK' : L ≤ Subgroup.normalizer (K' : Set G) := fun l hl =>
    CFSG.Walter.mem_normalizer_inf (le_normalizer_fstarZero H hl.2) (Subgroup.le_normalizer hl.1)
  have hK'p : IsPGroup p K' := hF.to_le (inf_le_left.trans (fstarZero_le H))
  have hFL : IsPGroup p (generalizedFittingSubgroupOf L) := by
    rcases hstep K' hK'1 hK'H hLK' with h | h
    · have hL : L = H ⊓ Subgroup.normalizer (K' : Set G) :=
        le_antisymm (le_inf inf_le_right hLK') (le_inf h inf_le_left)
      rw [hL]
      exact isPGroup_generalizedFitting_inf_normalizer hp hF hK'H hK'p
    · have hL : L = M ⊓ Subgroup.normalizer (K' : Set G) :=
        le_antisymm (le_inf inf_le_left hLK') (le_inf inf_le_left h)
      rw [hL]
      exact isPGroup_generalizedFitting_inf_normalizer hp hFM inf_le_right hK'p
  have hCL : Subgroup.centralizer (A : Set G) ≤ L := le_inf hCM hCH
  have hAL : A ≤ L := (le_centralizer hset).trans hCL
  have hLtop : L ≠ ⊤ := fun h => hHco.1 (top_le_iff.mp (h ▸ inf_le_right))
  have hK'N : K' ∈ sigN L A p := by
    refine ⟨le_inf inf_le_right hK'H, hK'p, hAL.trans hLK', ?_⟩
    refine le_oddCoreOf (inf_le_inf_right _ (le_inf inf_le_right hK'H)) ?_ ?_
    · intro c hc
      exact CFSG.Walter.mem_normalizer_inf (hLK' hc.1) (Subgroup.le_normalizer hc.2)
    · exact odd_card_of_isPGroup hp hp2 (hK'p.to_le inf_le_left)
  obtain ⟨P, hK'P, hP⟩ := (Set.toFinite (sigN L A p)).exists_le_maximal hK'N
  have hP1 : P ≠ ⊥ := fun h => hK'1 (le_bot_iff.mp (h ▸ hK'P))
  have hPL : P ≤ L := hP.1.1
  have hPp : IsPGroup p P := hP.1.2.1
  have hLZ := h311 G L A (isSStarIn_of_le hset hLtop hAL) p hp hp2 P hP hFL
  have hZH : CFSG.Glauberman.ZJ P ≤ H := (zj_le P).trans (hPL.trans inf_le_right)
  have hNPZ := normalizer_le_normalizer_zj P
  have hcase : ∀ M₁ : Subgroup G, IsCoatom M₁ → Subgroup.centralizer (A : Set G) ≤ M₁ →
      IsPGroup p (generalizedFittingSubgroupOf M₁) → L ≤ M₁ →
      M₁ ⊓ Subgroup.normalizer (P : Set G) ≤ L →
      Subgroup.normalizer (CFSG.Glauberman.ZJ P : Set G) = M₁ ∧
        Maximal (· ∈ sigN ⊤ A p) P := by
    intro M₁ hM₁ hCM₁ hFM₁ hLM₁ hN
    have hPM₁ : Maximal (· ∈ sigN M₁ A p) P := by
      refine maximal_sigN_of_forall
        ((mem_sigN_iff_of_le hCL hCM₁ hPL (hPL.trans hLM₁)).mp hP.1) ?_
      intro Q hQ hPQ hQN
      have hQM₁ : Q ≤ M₁ := hQ.1
      have hQL : Q ≤ L := (le_inf hQM₁ hQN).trans hN
      exact hP.2 ((mem_sigN_iff_of_le hCL hCM₁ hQL hQM₁).mpr hQ) hPQ
    exact normalizer_zj_eq_and_maximal h311 hset hp hp2 hM₁ hCM₁ hFM₁ hPM₁ hP1
  have hother : ∀ M₂ : Subgroup G, IsCoatom M₂ → Subgroup.centralizer (A : Set G) ≤ M₂ →
      IsPGroup p (generalizedFittingSubgroupOf M₂) → P ≤ M₂ → Maximal (· ∈ sigN ⊤ A p) P →
      Subgroup.normalizer (CFSG.Glauberman.ZJ P : Set G) = M₂ :=
    fun M₂ hM₂ hCM₂ hFM₂ hPM₂ hPG => (normalizer_zj_eq_and_maximal h311 hset hp hp2 hM₂ hCM₂
      hFM₂ (maximal_sigN_of_le hCM₂ le_top hPG hPM₂) hP1).1
  rcases hstep _ (zj_ne_bot hPp hP1) hZH hLZ with h | h
  ·
    obtain ⟨hNH, hPG⟩ := hcase H hHco hCH hF inf_le_right
      ((inf_le_inf_left H hNPZ).trans (le_inf h inf_le_left))
    exact hMH ((hother M hMco hCM hFM (hPL.trans inf_le_left) hPG).symm.trans hNH)
  ·
    obtain ⟨hNM, hPG⟩ := hcase M hMco hCM hFM inf_le_left
      ((inf_le_inf_left M hNPZ).trans (le_inf inf_le_left h))
    exact hMH (hNM.symm.trans (hother H hHco hCH hF (hPL.trans inf_le_right) hPG))

end G62

open G62 in
theorem G62_of (h311 : S_G311) (h51 : S_G51) (h61 : S_G61) (h37 : S_G37) : S_G62 := by
  intro G _ _ S A hset a haA ha1 H hH p hp hp2 hF
  have := hset.isSimpleGroup
  have : Fact p.Prime := ⟨hp⟩
  have ha2 : orderOf a = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (hset.elem.2 a haA) ha1
  have haH : a ∈ H := mem_of_mem_benderM hH
  have hCH : Subgroup.centralizer (A : Set G) ≤ H :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA)).trans
      (centralizer_le_of_mem_benderM hH)
  have hAH : A ≤ H := (le_centralizer hset).trans hCH
  have hP₀p : IsPGroup p (fstarZero H) := hF.to_le (fstarZero_le H)
  have hP₀a : ⁅Subgroup.zpowers a, fstarZero H⁆ ≠ ⊥ := by
    rw [Subgroup.commutator_comm]
    exact commutator_fstarZero_ne_bot hp hp2 hF haH ha2
  obtain ⟨A₁, hA₁A, hA₁i, hA₁c⟩ := exists_hyperplane_commutator_ne_bot hset.elem haA ha1
    (hAH.trans (le_normalizer_fstarZero H)) (odd_card_of_isPGroup hp hp2 hP₀p) hP₀a
  have hM₁ : ∀ a₁ ∈ A₁, a₁ ≠ 1 → benderM a₁ = {H} := by
    intro a₁ ha₁ ha₁1
    have hall : ∀ H₁ ∈ benderM a₁, H₁ = H := by
      intro H₁ hH₁
      have hC₁ : Subgroup.centralizer (A₁ : Set G) ≤ H₁ :=
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha₁)).trans
          (centralizer_le_of_mem_benderM hH₁)
      refine eq_of_commutator_ne_bot h311 h51 h37 hset haA ha1 hH hp hp2 hF
        (isCoatom_of_mem_benderM hH₁) ((Subgroup.centralizer_le hA₁A).trans hC₁) ?_
      intro h
      apply hA₁c
      rw [Subgroup.commutator_comm]
      exact le_bot_iff.mp ((Subgroup.commutator_mono (inf_le_inf_left _ hC₁) le_rfl).trans h.le)
    obtain ⟨H₁, hH₁⟩ := benderM_nonempty hset ha₁1
    have hH₁H := hall H₁ hH₁
    rw [hH₁H] at hH₁
    exact Set.eq_singleton_iff_unique_mem.mpr ⟨hH₁, hall⟩
  obtain ⟨-, hA₁eq⟩ := h61 G S A hset a haA ha1 H hH A₁ hA₁A hA₁i hM₁
  have haA₁ : a ∈ A₁ := by
    rw [hA₁eq]
    exact Subgroup.mem_zpowers a
  apply hA₁c
  rw [commutator_zpowers_eq_bot_iff]
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp hx.2 a haA₁).symm

end CFSG.Goldschmidt
