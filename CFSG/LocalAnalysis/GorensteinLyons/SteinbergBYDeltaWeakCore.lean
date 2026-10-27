module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLDeltaNormalizerCentralProduct
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

namespace DeltaWeakCore

theorem not_dvd_card_of_isPGroup_two [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : Subgroup G} (hQ : IsPGroup 2 Q) : ¬ p ∣ Nat.card Q := by
  have := Fact.mk Nat.prime_two
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  rw [hn]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

theorem normalizer_le_weakCore [Finite G] {p : ℕ} {P E : Subgroup G} (hEP : E ≤ P)
    (h2 : 2 ≤ CFSG.Open.pRank p E)
    (h3 : 3 ≤ CFSG.Open.pRank p (E ⊔ (P ⊓ centralizer (E : Set G)))) :
    normalizer (E : Set G) ≤ GLAWeakCore p P :=
  le_sSup ⟨E, hEP, h2, h3, rfl⟩

theorem map_centralizer_mulEquiv (φ : G ≃* G) (Q : Subgroup G) :
    (centralizer (Q : Set G)).map φ.toMonoidHom =
      centralizer ((Q.map φ.toMonoidHom : Subgroup G) : Set G) := by
  ext x
  rw [mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · rintro h _ ⟨q, hq, rfl⟩
    have h1 := h q hq
    apply φ.symm.injective
    rw [map_mul, map_mul, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact h1
  · intro h q hq
    have h1 := h (φ q) ⟨q, hq, rfl⟩
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h1

theorem weakCore_map_le [Finite G] {p : ℕ} (hp : 1 < p) (P : Subgroup G) (φ : G ≃* G) :
    GLAWeakCore p (P.map φ.toMonoidHom) ≤ (GLAWeakCore p P).map φ.toMonoidHom := by
  apply sSup_le
  rintro _ ⟨Q', hQ'P, h2, h3, rfl⟩
  set Q := Q'.map φ.symm.toMonoidHom with hQ
  have hPP : (P.map φ.toMonoidHom).map φ.symm.toMonoidHom = P := by
    ext x
    simp
  have hQQ' : Q.map φ.toMonoidHom = Q' := by
    ext x
    simp [hQ]
  have hQP : Q ≤ P := hPP ▸ map_mono hQ'P
  have hQ2 : 2 ≤ CFSG.Open.pRank p Q :=
    h2.trans (CFSG.SectionRank.pRank_le_map hp φ.symm.toMonoidHom φ.symm.injective Q')
  have hmapY : (Q' ⊔ (P.map φ.toMonoidHom ⊓ centralizer (Q' : Set G))).map φ.symm.toMonoidHom =
      Q ⊔ (P ⊓ centralizer (Q : Set G)) := by
    rw [Subgroup.map_sup, map_inf_eq _ _ _ φ.symm.injective, hPP, map_centralizer_mulEquiv]
  have hQ3 : 3 ≤ CFSG.Open.pRank p (Q ⊔ (P ⊓ centralizer (Q : Set G))) := by
    rw [← hmapY]
    exact h3.trans (CFSG.SectionRank.pRank_le_map hp φ.symm.toMonoidHom φ.symm.injective _)
  have hN := normalizer_le_weakCore hQP hQ2 hQ3
  rw [← hQQ', ← map_equiv_normalizer_eq]
  exact map_mono hN

theorem le_inSubgroup_pCore_and_isCharacteristicP {p : ℕ} {Y L : Subgroup G}
    (hY : IsCharacteristicP p Y) (hLY : L ≤ Y) (hOL : CFSG.inSubgroup (CFSG.pCore p) Y ≤ L) :
    CFSG.inSubgroup (CFSG.pCore p) Y ≤ CFSG.inSubgroup (CFSG.pCore p) L ∧
      IsCharacteristicP p L := by
  have hn : ((CFSG.inSubgroup (CFSG.pCore p) Y).subgroupOf L).Normal :=
    (normal_subgroupOf_iff_le_normalizer hOL).mpr
      (hLY.trans (le_normalizer_inSubgroup_pCore p Y))
  have hle := le_inSubgroup_pCore_of_normal hOL hn (isPGroup_inSubgroup_pCore p Y)
  refine ⟨hle, fun x hx => ?_⟩
  have hxC : (x : G) ∈ centralizer (CFSG.inSubgroup (CFSG.pCore p) Y : Set G) := by
    rw [mem_centralizer_iff]
    intro q hq
    obtain ⟨q', hq', rfl⟩ := hle hq
    exact congrArg Subtype.val (mem_centralizer_iff.mp hx q' hq')
  have hxY : zpowers (x : G) ≤ CFSG.inSubgroup (CFSG.pCore p) Y :=
    le_inSubgroup_pCore_of_le_centralizer hY ((zpowers_le).mpr (hLY x.2))
      ((zpowers_le).mpr hxC)
  obtain ⟨y, hy, hyx⟩ := hle (hxY (mem_zpowers (x : G)))
  rw [show y = x from Subtype.ext hyx] at hy
  exact hy

end DeltaWeakCore

open DeltaWeakCore

theorem delta_weak_core_contains_local_two_cores [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hchar : IsCharacteristicPType G 2) {p : ℕ}
    (hp : p ∈ GLABeta 4 G) (hfail : ¬ GLADeltaZero G p) {B D₀ S₀ : Subgroup G}
    (hB : GLAIsBmax p B) (hD₀B : D₀ ≤ B) (hD₀ : IsElemAbelian p D₀)
    (hD₀card : Nat.card D₀ = p ^ 2) (hW : IsDeltaSeedWitness p B D₀ S₀) {S : Subgroup G}
    (hS : Maximal (· ∈ deltaSeededFamily p B S₀) S) {A H Q R : Subgroup G}
    (hA : A = B ⊓ centralizer (S : Set G)) (hH : H = normalizer (S : Set G))
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) H) (hR : R = Q ⊓ centralizer (S : Set G))
    {F : Subgroup G → Subgroup G} (hF : ∀ D : Subgroup G, F D = Q ⊓ centralizer (D : Set G))
    {L : Set (Subgroup G)} (hL : L = {D | D ≤ A ∧ Nat.card D = p ∧ S < F D})
    {M : Subgroup G} (hM : M ∈ maximalTwoLocalsContaining (H : Set G))
    (P : Sylow p G) (hBP : B ≤ (P : Subgroup G)) :
    CFSG.Open.pRank p B = GLATwoLocalRank p G ∧ 4 ≤ GLATwoLocalRank p G ∧
    B ≤ GLAWeakCore p (P : Subgroup G) ∧
    (∀ E : Subgroup G, E ≤ B → 2 ≤ CFSG.Open.pRank p E →
      normalizer (E : Set G) ≤ GLAWeakCore p (P : Subgroup G)) ∧
    (∀ K : Subgroup G, B ≤ normalizer (K : Set G) → ¬ p ∣ Nat.card K →
      K ≤ GLAWeakCore p (P : Subgroup G)) ∧
    S₀ ≤ S ∧ S ≤ Q ∧ Q ≤ GLAWeakCore p (P : Subgroup G) ∧
    CFSG.inSubgroup (CFSG.pCore 2) M ≤ GLAWeakCore p (P : Subgroup G) ∧
    (∀ D ∈ L, F D ≤ GLAWeakCore p (P : Subgroup G)) ∧ R ≤ GLAWeakCore p (P : Subgroup G) ∧
    (∀ Y : Subgroup G, IsPLocal 2 Y → B ≤ Y →
      B ≤ GLAWeakCore p (P : Subgroup G) ⊓ Y ∧ CFSG.inSubgroup (CFSG.pCore 2) Y ≠ ⊥ ∧
      CFSG.inSubgroup (CFSG.pCore 2) Y ≤
        CFSG.inSubgroup (CFSG.pCore 2) (GLAWeakCore p (P : Subgroup G) ⊓ Y) ∧
      IsCharacteristicP 2 (GLAWeakCore p (P : Subgroup G) ⊓ Y : Subgroup G) ∧
      CFSG.Open.pRank p (GLAWeakCore p (P : Subgroup G) ⊓ Y) = CFSG.Open.pRank p Y ∧
      CFSG.Open.pRank p Y = GLATwoLocalRank p G) ∧
    (IsPLocal 2 H ∧ B ≤ H) ∧ (IsPLocal 2 M ∧ B ≤ M) ∧
    (∀ D ∈ L, IsPLocal 2 (normalizer (F D : Set G)) ∧ B ≤ normalizer (F D : Set G)) ∧
    (¬ GLAWeakCoreLocal G p →
      CFSG.inSubgroup (CFSG.pCore 2) (GLAWeakCore p (P : Subgroup G)) = ⊥) := by
  classical
  have hpp : p.Prime := hp.1
  have hp2 : p ≠ 2 := hp.2.1
  have hp1 : 1 < p := hpp.one_lt
  have := Fact.mk hpp
  have h4 : 4 ≤ GLATwoLocalRank p G := hp.2.2.2
  obtain ⟨hBr, hYr⟩ := DeltaNormalizer.pRank_eq_twoLocalRank_of_isBmax hp1 hB
  set W := GLAWeakCore p (P : Subgroup G) with hWdef
  have hBL := delta_normalizer_central_product_and_line_fixed_subgroups hnab hchar hp hfail hB
    hD₀B hD₀ hD₀card hW hS hA hH hQ hR rfl hF hL
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hLD, -⟩ := hBL
  have hBX := ((delta_seeded_maximal_local_rank_two_centralizer hnab hchar hp hfail).2 B D₀ S₀
    hB hD₀B hD₀ hD₀card hW).2 S hS
  rw [← hA, ← hH, ← hQ] at hBX
  obtain ⟨-, -, hMfacts, -, hSQ, -⟩ := hBX
  obtain ⟨-, -, -, -, hS₀ne, -⟩ := hW
  have hS2 : IsPGroup 2 S := hS.1.1
  have hS₀S : S₀ ≤ S := hS.1.2.1
  have hBH : B ≤ H := hH ▸ hS.1.2.2.1
  have hSne : S ≠ ⊥ := fun h => hS₀ne (le_bot_iff.mp (h ▸ hS₀S))
  have hHloc : IsPLocal 2 H := ⟨S, hSne, hS2, hH⟩
  have hHM : H ≤ M := fun x hx => hM.2 hx
  have hBM : B ≤ M := hBH.trans hHM
  have hBne : B ≠ ⊥ := by
    intro h
    have h1 : Nat.card B = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hB.2.1] at h1
    have h2 := Nat.one_lt_pow (by omega : GLATwoLocalRank p G ≠ 0) hp1
    omega
  have hBcent : ∀ E : Subgroup G, E ≤ B →
      B ≤ (P : Subgroup G) ⊓ centralizer (E : Set G) := by
    intro E hEB
    refine le_inf hBP fun b hb => mem_centralizer_iff.mpr fun e he => ?_
    exact congrArg Subtype.val (hB.1.1.is_comm.comm ⟨e, hEB he⟩ ⟨b, hb⟩)
  have hEW : ∀ E : Subgroup G, E ≤ B → 2 ≤ CFSG.Open.pRank p E →
      normalizer (E : Set G) ≤ W := by
    intro E hEB hE2
    refine normalizer_le_weakCore (hEB.trans hBP) hE2 ?_
    have h1 := CFSG.SectionRank.pRank_mono hp1 ((hBcent E hEB).trans (le_sup_right (a := E)))
    rw [hBr] at h1
    omega
  have hBW : B ≤ W := le_normalizer.trans (hEW B le_rfl (by rw [hBr]; omega))
  have hKW : ∀ K : Subgroup G, B ≤ normalizer (K : Set G) → ¬ p ∣ Nat.card K → K ≤ W := by
    intro K hBK hKp
    refine le_of_forall_hyperplane_centralizer_le hpp hB.1 hBne hBK hKp fun E hEB hEidx => ?_
    have hEcard : Nat.card E = p ^ (GLATwoLocalRank p G - 1) := by
      have h1 := Subgroup.relIndex_mul_card E B
      rw [inf_eq_left.mpr hEB, hEidx, hB.2.1] at h1
      have h2 : p ^ GLATwoLocalRank p G = p * p ^ (GLATwoLocalRank p G - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega)]
      rw [h2] at h1
      exact Nat.eq_of_mul_eq_mul_left (by omega) h1
    have hE2 : 2 ≤ CFSG.Open.pRank p E := by
      have := CFSG.SectionRank.le_pRank hp1 le_rfl (isElemAbelian_of_le_elem hEB hB.1) hEcard
      omega
    exact inf_le_right.trans ((centralizer_le_normalizer _).trans (hEW E hEB hE2))
  have hO2W : ∀ Y : Subgroup G, B ≤ Y → CFSG.inSubgroup (CFSG.pCore 2) Y ≤ W := fun Y hBY =>
    hKW _ (hBY.trans (le_normalizer_inSubgroup_pCore 2 Y))
      (not_dvd_card_of_isPGroup_two hpp hp2 (isPGroup_inSubgroup_pCore 2 Y))
  have hQW : Q ≤ W := hQ ▸ hO2W H hBH
  have hYfacts : ∀ Y : Subgroup G, IsPLocal 2 Y → B ≤ Y →
      B ≤ W ⊓ Y ∧ CFSG.inSubgroup (CFSG.pCore 2) Y ≠ ⊥ ∧
      CFSG.inSubgroup (CFSG.pCore 2) Y ≤ CFSG.inSubgroup (CFSG.pCore 2) (W ⊓ Y) ∧
      IsCharacteristicP 2 (W ⊓ Y : Subgroup G) ∧
      CFSG.Open.pRank p (W ⊓ Y) = CFSG.Open.pRank p Y ∧
      CFSG.Open.pRank p Y = GLATwoLocalRank p G := by
    intro Y hY hBY
    obtain ⟨hle, hcharL⟩ := le_inSubgroup_pCore_and_isCharacteristicP (hchar Y hY)
      (inf_le_right : W ⊓ Y ≤ Y) (le_inf (hO2W Y hBY) (map_subtype_le _))
    refine ⟨le_inf hBW hBY, inSubgroup_pCore_ne_bot_of_isPLocal hY, hle, hcharL, ?_,
      hYr Y hY hBY⟩
    refine le_antisymm (CFSG.SectionRank.pRank_mono hp1 inf_le_right) ?_
    rw [hYr Y hY hBY, ← hBr]
    exact CFSG.SectionRank.pRank_mono hp1 (le_inf hBW hBY)
  refine ⟨hBr, h4, hBW, hEW, hKW, hS₀S, hSQ, hQW, hO2W M hBM,
    fun D _ => (hF D ▸ inf_le_left).trans hQW, (hR ▸ inf_le_left).trans hQW, hYfacts,
    ⟨hHloc, hBH⟩, ⟨hM.1.1, hBM⟩, fun D hD => ⟨(hLD D hD).2.2.2.2.1, (hLD D hD).2.2.1⟩, ?_⟩
  intro hnwc
  by_contra hO
  apply hnwc
  refine ⟨?_, fun P' => ?_⟩
  · have h1 := CFSG.SectionRank.pRank_mono hp1 (le_top : B ≤ ⊤)
    rw [hBr] at h1
    omega
  · obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P'
    set O := CFSG.inSubgroup (CFSG.pCore 2) W with hOdef
    refine ⟨normalizer ((O.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G),
      ⟨O.map (MulAut.conj g).toMonoidHom, ?_, (isPGroup_inSubgroup_pCore 2 W).map _, rfl⟩, ?_⟩
    · intro h
      apply hO
      rw [eq_bot_iff]
      intro x hx
      have h1 : (MulAut.conj g).toMonoidHom x ∈ O.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
      rw [h, mem_bot] at h1
      rw [mem_bot]
      exact (MulAut.conj g).injective (h1.trans (map_one _).symm)
    · have hP' : ((P' : Sylow p G) : Subgroup G) =
          (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
        rw [← hg]
        rfl
      rw [hP']
      refine (weakCore_map_le hp1 (P : Subgroup G) (MulAut.conj g)).trans ?_
      rw [← map_equiv_normalizer_eq]
      exact map_mono (le_normalizer_inSubgroup_pCore 2 W)

end CFSG.LocalAnalysis.GorensteinLyons
