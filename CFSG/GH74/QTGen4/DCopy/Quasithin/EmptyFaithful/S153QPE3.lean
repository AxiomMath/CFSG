module

public import CFSG.Quasithin.EmptyFaithful.S153QPE3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153QPD6

public section

namespace CFSG.Quasithin.He17

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.He9
  CFSG.Quasithin.He16 CFSG.Quasithin.QP CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom)
open scoped commutatorElement

section PartB

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5}

theorem false_of_c27_e_F4 (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (c : Ctx15204 T Mc M H K₁ K₂ π) {Lc : Subgroup G} (tail : Tail15204 c Lc)
    (hYL : yOf152 T Mc M ≤ Lc) (hq : CFSG.IsQuasisimple ↥(modO2Image (g0Of T Mc M K₁) Lc))
    (he : IsSp4Block Lc ∧
      IsMaxParabolic2 (autOn Lc (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁))))
        (autOn ((M ⊓ g0Of T Mc M K₁) ⊓ Lc)
          (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁))))) : False := by
  classical
  obtain ⟨hsp, hmax⟩ := he
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set R := rOf T Mc M K₁ with hR
  set V := omegaOneCenterOf (pCoreOf 2 (Lc ⊔ R)) with hV
  have hLG : Lc ≤ g0Of T Mc M K₁ := le_of_mem_cComp tail.comp
  have hNG : g0Of T Mc M K₁ ≤ Subgroup.normalizer (Lc : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).1 tail.normal
  have hRG : R ≤ g0Of T Mc M K₁ := tail.hyp.radical.1
  have hRN : R ≤ Subgroup.normalizer (Lc : Set G) := hRG.trans hNG
  obtain ⟨hJV, hD, hOC⟩ := SBc17.inner_facts_F4 (hC27 G) tail.hyp tail.comp
    (isQuasisimple_quot tail.comp hq) tail.charTwo tail.not_le hRN
  obtain ⟨F, hF, hFin, hcard, e, hkerE⟩ := exists_equiv_of_isSp4Block hJV hD hOC hsp
  have hchar : CharP F 2 := SBc17.charP_two_of_card_eq_pow (n := 2) (by rw [hcard]; norm_num)
  have : Finite F := Finite.of_fintype F
  obtain ⟨y, hyY, hyN, hy5⟩ := exists_five_element_F4 (hC27 G) c tail hYL hq
  set Y := yOf152 T Mc M with hY
  have hYM1 : Y ≤ (M ⊓ g0Of T Mc M K₁) ⊓ Lc := Y_le_inf c hYL
  have hYN : ∀ b ∈ (M ⊓ g0Of T Mc M K₁) ⊓ Lc, ∀ k ∈ Y, b * k * b⁻¹ ∈ Y := fun b hb k hk =>
    (Subgroup.mem_normalizer_iff.mp (c.y.normal hb.1.1) k).mp hk
  let π₁ := SBc17.actHom hJV
  let φ : ↥Lc →* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) := e.toMonoidHom.comp π₁
  let ψY : ↥Y →* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) := φ.comp (Subgroup.inclusion hYL)
  set N : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) := ψY.range with hN
  set O := pCoreOf 2 Y with hO
  have hOY : O ≤ Y := pCoreOf_le 2 Y
  set O' : Subgroup ↥Y := O.subgroupOf Y with hO'
  have hO'n : O'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOY).2
    (le_normalizer_pCoreOf 2 Y)
  have hO'idx : O'.index = 5 := c.y.relIndex_five
  have hO'card : Nat.card (↥Y ⧸ O') = 5 := by
    rw [← Subgroup.index, hO'idx]
  set Mm : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) := O'.map ψY with hMm
  have hMN : Mm ≤ N := Subgroup.map_le_range ψY O'
  have hO'p : IsPGroup 2 ↥O' := (pCoreOf_isPGroup 2 Y).of_equiv (Subgroup.subgroupOfEquivOfLe hOY).symm
  have hM2 : IsPGroup 2 ↥Mm := hO'p.map ψY

  have hyL : y ∈ Lc := hYL hyY
  have hx5 : orderOf (ψY ⟨y, hyY⟩) = 5 := by
    have h1 : orderOf (π₁ ⟨y, hyL⟩) = 5 := by
      rw [← Subgroup.orderOf_coe]
      exact hy5
    show orderOf (e (π₁ ⟨y, hyL⟩)) = 5
    rw [MulEquiv.orderOf_eq]
    exact h1
  have hxN : ψY ⟨y, hyY⟩ ∈ N := ⟨⟨y, hyY⟩, rfl⟩
  have hxM : ψY ⟨y, hyY⟩ ∉ Mm := by
    intro hxM
    obtain ⟨j, hj⟩ := hM2 ⟨_, hxM⟩
    have h1 : (ψY ⟨y, hyY⟩) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have h2 : orderOf (ψY ⟨y, hyY⟩) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one h1
    rw [hx5] at h2
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h2) (by norm_num)

  have hrel : Mm.relIndex N ∣ 5 := by
    have h1 : Mm.relIndex N = (O' ⊔ ψY.ker).index := by
      rw [hMm, hN, MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
        Subgroup.relIndex_top_right]
    rw [h1, ← hO'idx]
    exact Subgroup.index_dvd_of_le le_sup_left
  have hrel1 : Mm.relIndex N ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    exact hxM (h1 hxN)
  have hrel5 : Mm.relIndex N = 5 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hrel with h | h
    · exact absurd h hrel1
    · exact h
  have hcardN : Nat.card N = 5 * Nat.card Mm := by
    have h1 := Subgroup.relIndex_mul_card (H := Mm) (K := N)
    rw [inf_eq_left.mpr hMN, hrel5] at h1
    exact h1.symm

  have hker_le : ψY.ker ≤ O' := by
    intro z hz
    have hz1 : ψY z = 1 := hz
    have hz2 : π₁ ⟨(z : G), hYL z.2⟩ = 1 := by
      have h1 : e (π₁ ⟨(z : G), hYL z.2⟩) = 1 := hz1
      apply e.injective
      rw [h1, map_one]
    have hzc : (z : G) ∈ pCoreOf 2 Lc := hkerE _ hz2
    have hle : Y ⊓ pCoreOf 2 Lc ≤ pCoreOf 2 Y := by
      refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        ((pCoreOf_isPGroup 2 Lc).to_le inf_le_right)
      intro y' hy'
      have hnp := le_normalizer_pCoreOf 2 Lc (hYL hy')
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hx1, hx2⟩
        exact ⟨Y.mul_mem (Y.mul_mem hy' hx1) (Y.inv_mem hy'),
          (Subgroup.mem_normalizer_iff.mp hnp x).mp hx2⟩
      · rintro ⟨hx1, hx2⟩
        refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hnp x).mpr hx2⟩
        have := Y.mul_mem (Y.mul_mem (Y.inv_mem hy') hx1) hy'
        simpa [mul_assoc] using this
    exact (Subgroup.mem_subgroupOf).2 (hle ⟨z.2, hzc⟩)

  have hMm_char : ∀ m ∈ N, (∃ k : ℕ, m ^ 2 ^ k = 1) → m ∈ Mm := by
    rintro m ⟨a, rfl⟩ ⟨k, hk⟩
    have h1 : a ^ 2 ^ k ∈ ψY.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hk
    have h2 : a ^ 2 ^ k ∈ O' := hker_le h1
    have h3 : a ∈ O' := mem_of_pow_two_mem_of_card_five hO'card h2
    exact ⟨a, h3, rfl⟩
  have hEM : ∀ (x : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)),
      (∀ n ∈ N, x * n * x⁻¹ ∈ N) → ∀ m ∈ Mm, x * m * x⁻¹ ∈ Mm := by
    intro x hx m hm
    obtain ⟨k, hk⟩ := hM2 ⟨m, hm⟩
    have hk' : m ^ 2 ^ k = 1 := congrArg Subtype.val hk
    refine hMm_char _ (hx m (hMN hm)) ⟨k, ?_⟩
    rw [conj_pow, hk', mul_one, mul_inv_cancel]

  have hP := isMaxParabolic2_top_of_mulEquiv hmax e
  set P : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) :=
    ((autOn ((M ⊓ g0Of T Mc M K₁) ⊓ Lc) V).subgroupOf (autOn Lc V)).map e.toMonoidHom with hPdef
  have hnormN : ∀ p ∈ P, ∀ n ∈ N, p * n * p⁻¹ ∈ N := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨a, rfl⟩
    have hs' : (s : MulAut ↥V) ∈ autOn ((M ⊓ g0Of T Mc M K₁) ⊓ Lc) V := hs
    obtain ⟨b, hbV, hb, hbs⟩ := SBc17.mem_autOn_iff.mp hs'
    have hbJ : b ∈ Lc := hb.2
    have hsπ : s = π₁ ⟨b, hbJ⟩ := Subtype.ext (by rw [SBc17.actHom_apply]; exact hbs.symm)
    refine ⟨⟨b * (a : G) * b⁻¹, hYN b hb a a.2⟩, ?_⟩
    have h1 : (⟨b * (a : G) * b⁻¹, hYL (hYN b hb a a.2)⟩ : ↥Lc) =
        ⟨b, hbJ⟩ * ⟨(a : G), hYL a.2⟩ * ⟨b, hbJ⟩⁻¹ := Subtype.ext (by simp)
    show φ ⟨b * (a : G) * b⁻¹, hYL (hYN b hb a a.2)⟩ = e.toMonoidHom s * φ ⟨(a : G), hYL a.2⟩ *
      (e.toMonoidHom s)⁻¹
    rw [h1, map_mul, map_mul, map_inv, hsπ]
    rfl
  obtain ⟨-, S, hSyl, hSN⟩ := hP.1
  have hU : IsSylowTwoOf (SymplecticFlag.unipotent 2 F) ⊤ := SzN2.isSylowTwoOf_unipotent
  obtain ⟨g, hg⟩ := exists_conj_isSylowTwoOf hU hSyl
  let E : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) :=
    (SymplecticTorusWeyl.torus 2 F).map (MulAut.conj g).toMonoidHom
  have hEP : E ≤ P := by
    rintro _ ⟨t, ht, rfl⟩
    apply hSN
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩
    have h1 : t ∈ Subgroup.normalizer (SymplecticFlag.unipotent 2 F :
        Set ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) := by
      rw [SymplecticHigher.normalizer_unipotent]
      exact SymplecticFlag.torus_le_borelSubgroup ht
    rw [hg, ← Subgroup.map_equiv_normalizer_eq (SymplecticFlag.unipotent 2 F) (MulAut.conj g)]
    exact ⟨t, h1, rfl⟩
  have hcardU : Nat.card Fˣ = 3 := by rw [Nat.card_units, Nat.card_eq_fintype_card, hcard]
  have hE3 : IsPGroup 3 ↥E := by
    rintro ⟨_, t, ⟨s, rfl⟩, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hs3 : s ^ 3 = 1 := by
      funext i
      have := pow_card_eq_one' (G := Fˣ) (x := s i)
      rwa [hcardU] at this
    show ((MulAut.conj g) (torusHom s)) ^ 3 ^ 1 = 1
    rw [pow_one, ← map_pow, ← map_pow, hs3, map_one, map_one]
  obtain ⟨n, hnN, hnM, hnE⟩ := exists_centralizing_mem_sdiff hMN hcardN hM2 hE3
    (fun e' he n hn => hnormN e' (hEP he) n hn) (fun e' he => hEM e' (hnormN e' (hEP he)))

  have hn3 : n ^ 3 = 1 := by
    have hcomm : ∀ s : Fin 2 → Fˣ,
        (g⁻¹ * n * g) * torusHom s = torusHom s * (g⁻¹ * n * g) := by
      intro s
      have h1 := hnE ((MulAut.conj g) (torusHom s)) ⟨torusHom s, ⟨s, rfl⟩, rfl⟩
      have h2 : (g * torusHom s * g⁻¹) * n = n * (g * torusHom s * g⁻¹) := by
        exact mul_inv_eq_iff_eq_mul.1 (by simpa using h1 : (g * torusHom s * g⁻¹) * n *
          (g * torusHom s * g⁻¹)⁻¹ = n)
      calc (g⁻¹ * n * g) * torusHom s = g⁻¹ * (n * (g * torusHom s * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * torusHom s * g⁻¹) * n) * g := by rw [h2]
        _ = torusHom s * (g⁻¹ * n * g) := by group
    have h3 := cube_eq_one_of_commute_torus (F := F) hcard hcomm
    have e3 : (g⁻¹ * n * g) ^ 3 = g⁻¹ * n ^ 3 * g := by
      have := conj_pow (a := g⁻¹) (b := n) (i := 3)
      simpa using this
    rw [e3] at h3
    simpa [mul_assoc] using congrArg (fun z => g * z * g⁻¹) h3
  have hn1 : n ≠ 1 := fun h => hnM (h ▸ Mm.one_mem)
  have hn3' : orderOf n = 3 := orderOf_eq_prime hn3 hn1
  have h3N : 3 ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨n, hnN⟩ : ↥N)
    rwa [Subgroup.orderOf_mk, hn3'] at this
  rw [hcardN] at h3N
  obtain ⟨j, hj⟩ := hM2.exists_card_eq
  rw [hj] at h3N
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 3)).1 h3N with h | h
  · exact absurd h (by norm_num)
  · exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h) (by norm_num)

end PartB

section Final

theorem input15204QuasiRest4_of_c27_F4
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G) : Input15204QuasiRest4_F4 := by
  intro G _ _ T Mc M H K₁ K₂ π c Lc tail hYL _ hq he
  exact false_of_c27_e_F4 hC27 c tail hYL hq he

theorem input15204QuasiRest3_proved_F4
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G) : Input15204QuasiRest3_F4 :=
  input15204QuasiRest3_of_rest4_F4 hC27 (input15204QuasiRest4_of_c27_F4 hC27)

theorem input15204BranchBQuasi_proved_F4
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G) : Input15204BranchBQuasi_F4 :=
  input15204BranchBQuasi_of_rest3_F4 hC27 (input15204QuasiRest3_proved_F4 hC27)

end Final

end CFSG.Quasithin.He17
