module

public import CFSG.Timmesfeld.ARS.CaseOASurj
public import CFSG.LargeExtraspecial.A2ModCfgSL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Module Matrix CFSG.RankThree.OrthogonalInvolutions CFSG.Timmesfeld.ARS CFSG.LieType
  CFSG.LieType.Universal
open CFSG.Timmesfeld (sroot upperUnipotent lowerUnipotent)
open scoped commutatorElement

variable {G : Type} [Group G] {R : Set (Subgroup G)}

theorem isConfig_comp {r r' : ℕ} {adj : Fin r → Fin r → Prop} {adj' : Fin r' → Fin r' → Prop}
    {A B : Fin r → Subgroup G} (hX : IsConfig R adj A B) {f : Fin r' → Fin r}
    (hf : Function.Injective f) (hadj : ∀ i j, adj' i j ↔ adj (f i) (f j)) :
    IsConfig R adj' (A ∘ f) (B ∘ f) where
  memA k := hX.memA (f k)
  memB k := hX.memB (f k)
  opp k := hX.opp (f k)
  edge i j h := hX.edge (f i) (f j) ((hadj i j).mp h)
  nonadj i j hij h1 h2 := hX.nonadj (f i) (f j) (hf.ne hij) (fun h => h1 ((hadj i j).mpr h))
    (fun h => h2 ((hadj j i).mpr h))

theorem eq_of_mem_zpowers {d x : G} (hd : d * d = 1) (hx : x ∈ Subgroup.zpowers d)
    (hx1 : x ≠ 1) : x = d := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : d ^ (2 : ℤ) = 1 := by rw [zpow_two, hd]
  obtain ⟨l, rfl | rfl⟩ := Int.even_or_odd' n
  · exact absurd (by rw [_root_.zpow_mul, h2, _root_.one_zpow]) hx1
  · rw [_root_.zpow_add, _root_.zpow_mul, h2, _root_.one_zpow, one_mul, zpow_one]

theorem mul_self_and_ne_one_of_mem (hR : IsRootClass R) {E : Subgroup G} (hE : E ∈ R)
    {d : G} (hEd : E = Subgroup.zpowers d) : d * d = 1 ∧ d ≠ 1 := by
  refine ⟨hR.mul_self E hE d (hEd ▸ Subgroup.mem_zpowers d), fun h => hR.ne_bot E hE ?_⟩
  rw [hEd, h, Subgroup.zpowers_one_eq_bot]

theorem card_eq_two_of_mem (hR : IsRootClass R) {E : Subgroup G} (hE : E ∈ R) {d : G}
    (hEd : E = Subgroup.zpowers d) : Nat.card E = 2 := by
  obtain ⟨hd, hd1⟩ := mul_self_and_ne_one_of_mem hR hE hEd
  rw [hEd, Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two, hd]) hd1

section Members

variable {D : Set G}

theorem A2Action.commSpaceOf_top_eq_top {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {ρ : G →* (V ≃ₗ[ZMod 2] V)} (hA : A2Action D Q ρ) {d : G}
    (hd : d ∈ D) (hirr : ∀ W : Submodule (ZMod 2) V, (∀ x, ∀ w ∈ W, ρ x w ∈ W) → W = ⊥ ∨ W = ⊤) :
    commSpaceOf ρ ⊤ = ⊤ :=
  A2Mod.commSpaceOf_top_eq_top ρ hirr (x := d)
    fun h => hA.ne_one hd (hA.injective (h.trans (map_one ρ).symm))

theorem card_eq_two_of_forall_eq_zpowers (hR : IsRootClass R)
    (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d) : ∀ E ∈ R, Nat.card E = 2 := fun E hE => by
  obtain ⟨d, -, hd⟩ := hRD E hE
  exact card_eq_two_of_mem hR hE hd

theorem mem_of_eq_zpowers {E : Subgroup G} {d : G} (h : E = Subgroup.zpowers d) : d ∈ E :=
  h ▸ Subgroup.mem_zpowers d

end Members

theorem map_mem_of_elemTv_mem {k : ℕ} {D : Set G} (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (Ψ : SpecialLinearGroup (Fin k) (ZMod 2) →* G) {i j : Fin k} (hij : i ≠ j)
    (h : Ψ (elemTv i j) ∈ D) : ∀ g ∈ transvectionSet k (ZMod 2), Ψ g ∈ D := by
  intro g hg
  rw [← conjugatesOf_transvection hij] at hg
  obtain ⟨c, rfl⟩ := isConj_iff.mp hg
  rw [map_mul, map_mul, map_inv, ← elemTv_eq_transvection hij]
  exact hDc _ _ h

theorem map_elemTv_eq_of_map_rootGroup {m : ℕ}
    (Ψ : SpecialLinearGroup (Fin (m + 1)) (ZMod 2) →* G) {γ : Fin m → ℤ} {i j : Fin (m + 1)}
    (hij : i ≠ j) (hγ : SpecialLinear.toStd m γ = Pi.single i 1 - Pi.single j 1) {d : G}
    (hd1 : d ≠ 1)
    (h : ((SpecialLinear.rootDatum m (ZMod 2)).rootGroup γ).map Ψ = Subgroup.zpowers d) :
    Ψ (elemTv i j) = d := by
  have hd : d ∈ ((SpecialLinear.rootDatum m (ZMod 2)).rootGroup γ).map Ψ :=
    h ▸ Subgroup.mem_zpowers d
  obtain ⟨g, hg, rfl⟩ := hd
  change g ∈ SpecialLinear.rootGroup m (ZMod 2) γ at hg
  rw [SpecialLinear.rootGroup_eq m (ZMod 2) hij hγ, SpecialLinear.mem_rootSubgroup] at hg
  obtain ⟨c, rfl⟩ := hg
  rcases zmodTwo_eq_zero_or_one c with rfl | rfl
  · rw [SpecialLinearGroup.transvection_coeff_zero, map_one] at hd1
    exact absurd rfl hd1
  · rw [elemTv_eq_transvection hij]

theorem map_elemTv_castSucc_succ {m : ℕ} (Ψ : SpecialLinearGroup (Fin (m + 1)) (ZMod 2) →* G)
    (j : Fin m) {d : G} (hd1 : d ≠ 1)
    (h : ((SpecialLinear.rootDatum m (ZMod 2)).rootGroup (sroot j)).map Ψ = Subgroup.zpowers d) :
    Ψ (elemTv j.castSucc j.succ) = d :=
  map_elemTv_eq_of_map_rootGroup Ψ Fin.castSucc_lt_succ.ne (SpecialLinear.toStd_single m j) hd1 h

theorem map_elemTv_succ_castSucc {m : ℕ} (Ψ : SpecialLinearGroup (Fin (m + 1)) (ZMod 2) →* G)
    (j : Fin m) {d : G} (hd1 : d ≠ 1)
    (h : ((SpecialLinear.rootDatum m (ZMod 2)).rootGroup (-sroot j)).map Ψ =
      Subgroup.zpowers d) :
    Ψ (elemTv j.succ j.castSucc) = d :=
  map_elemTv_eq_of_map_rootGroup Ψ Fin.castSucc_lt_succ.ne'
    (by rw [SpecialLinear.toStd_neg, SpecialLinear.toStd_single, neg_sub]) hd1 h

theorem exists_levi_zmodTwo [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    (h2 : ∀ E ∈ R, Nat.card E = 2) {m : ℕ} (hm : 3 ≤ m) {A B : Fin m → Subgroup G}
    (hX : IsConfig R (CFSG.Timmesfeld.ARS.edgeA m) A B) :
    ∃ Ψ : SpecialLinearGroup (Fin (m + 1)) (ZMod 2) →* G,
      (∀ j : Fin m, ((SpecialLinear.rootDatum m (ZMod 2)).rootGroup (sroot j)).map Ψ = A j) ∧
      (∀ j : Fin m, ((SpecialLinear.rootDatum m (ZMod 2)).rootGroup (-sroot j)).map Ψ = B j) := by
  set L : Subgroup G := ⨆ k, (A k ⊔ B k)
  have hle : ∀ k, A k ⊔ B k ≤ L := fun k => le_iSup (fun k => A k ⊔ B k) k
  obtain ⟨n, -, hcard, ρ, hρ, hedge⟩ := hX.exists_frame hR hiso (isRootedTree_A (by omega))
  obtain rfl : n = 1 := by
    have h := hcard _ (hX.memA ⟨0, by omega⟩)
    rw [h2 _ (hX.memA _)] at h
    exact Nat.pow_right_injective le_rfl (h.symm.trans (pow_one 2).symm)
  have hρL : ∀ k g, ρ k g ∈ L := fun k g => by
    have hr : (ρ k).range = A k ⊔ B k := by
      rw [MonoidHom.range_eq_map, ← NaturalModule.upperUnipotent_sup_lowerUnipotent,
        Subgroup.map_sup, (hρ k).2.1, (hρ k).2.2]
    exact hle k (hr ▸ ⟨g, rfl⟩)
  have hnonadj : ∀ i j, i ≠ j → ¬ CFSG.Timmesfeld.ARS.edgeA m i j →
      ¬ CFSG.Timmesfeld.ARS.edgeA m j i →
      Commuting ((A i).subgroupOf L) ((A j).subgroupOf L) ∧
      Commuting ((A i).subgroupOf L) ((B j).subgroupOf L) ∧
      Commuting ((B i).subgroupOf L) ((A j).subgroupOf L) ∧
      Commuting ((B i).subgroupOf L) ((B j).subgroupOf L) := by
    intro i j hij h1 h2
    obtain ⟨c1, c2, c3, c4⟩ := hX.nonadj i j hij h1 h2
    have hA := fun k => le_sup_left.trans (hle k)
    have hB := fun k => le_sup_right.trans (hle k)
    exact ⟨(Sec13Restrict.commuting_subgroupOf_iff' (hA i) (hA j)).2 c1,
      (Sec13Restrict.commuting_subgroupOf_iff' (hA i) (hB j)).2 c2,
      (Sec13Restrict.commuting_subgroupOf_iff' (hB i) (hA j)).2 c3,
      (Sec13Restrict.commuting_subgroupOf_iff' (hB i) (hB j)).2 c4⟩
  have hnt : ∃ k, ∃ a ∈ (A k).subgroupOf L, a ≠ 1 := by
    obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hX.memA ⟨0, by omega⟩)
    refine ⟨⟨0, by omega⟩, ⟨a, le_sup_left.trans (hle _) ha⟩, ha, fun h => ha1 ?_⟩
    exact congrArg Subtype.val h
  have hF : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 one_ne_zero
  obtain ⟨Ψ, hΨA, hΨB, -, -⟩ :=
    exists_surjective_of_rho (D := SpecialLinear.rootDatum m (GaloisField 2 1))
      (CurtisTits.curtisTitsConclusion_specialLinear (statedLieAdmissible_PSL_two_one (by omega))
        hF hm)
      (CFSG.Timmesfeld.leviConePresented_specialLinear m (GaloisField 2 1))
      (simplyLacedLevis_specialLinear m (GaloisField 2 1))
      hnonadj (fun k => (ρ k).codRestrict L (hρL k))
      (fun k => ⟨map_codRestrict_eq _ _ (le_sup_left.trans (hle k)) (hρ k).2.1,
        map_codRestrict_eq _ _ (le_sup_right.trans (hle k)) (hρ k).2.2⟩)
      (fun i j hij => by
        obtain ⟨ψ, hψ⟩ := hedge i j hij
        have hψL : ∀ g, ψ g ∈ L := by
          have hfund : ∀ (k : Fin 2) (s : Bool),
              SpecialLinear.fundamentalRootSubgroup 2 (GaloisField 2 1) k s ≤ L.comap ψ := by
            intro k s x hx
            cases s
            · change x ∈ SpecialLinear.rootSubgroup 2 (GaloisField 2 1) _ at hx
              obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup _ x).1 hx
              rw [Subgroup.mem_comap, ← CFSG.Timmesfeld.tv_of_ne]
              fin_cases k
              · exact (hψ c).2.1 ▸ hρL i _
              · exact (hψ c).2.2.2 ▸ hρL j _
            · change x ∈ SpecialLinear.rootSubgroup 2 (GaloisField 2 1) _ at hx
              obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup _ x).1 hx
              rw [Subgroup.mem_comap, ← CFSG.Timmesfeld.tv_of_ne]
              fin_cases k
              · exact (hψ c).1 ▸ hρL i _
              · exact (hψ c).2.2.1 ▸ hρL j _
          intro g
          have htop :
              (⊤ : Subgroup (SpecialLinearGroup (Fin (2 + 1)) (GaloisField 2 1))) ≤ L.comap ψ := by
            rw [← SpecialLinear.iSup_fundamentalRootSubgroup_eq_top]
            exact iSup_le fun k => iSup_le fun s => hfund k s
          exact htop (Subgroup.mem_top g)
        refine ⟨ψ.codRestrict L hψL, fun c => ?_⟩
        obtain ⟨h1, h2, h3, h4⟩ := hψ c
        exact ⟨Subtype.ext h1, Subtype.ext h2, Subtype.ext h3, Subtype.ext h4⟩)
      (iSup_subgroupOf_eq_top_of_iSup_eq rfl) hnt
  refine ⟨L.subtype.comp (Ψ.comp (slEquiv galoisFieldTwoOneEquiv).symm.toMonoidHom),
    fun j => ?_, fun j => ?_⟩
  · rw [← Subgroup.map_map]
    refine (congrArg (Subgroup.map L.subtype)
      (map_comp_slEquiv_symm_rootGroup galoisFieldTwoOneEquiv Ψ (sroot j))).trans ?_
    exact (congrArg (Subgroup.map L.subtype) (hΨA j)).trans
      (Subgroup.map_subgroupOf_eq_of_le (le_sup_left.trans (hle j)))
  · rw [← Subgroup.map_map]
    refine (congrArg (Subgroup.map L.subtype)
      (map_comp_slEquiv_symm_rootGroup galoisFieldTwoOneEquiv Ψ (-sroot j))).trans ?_
    exact (congrArg (Subgroup.map L.subtype) (hΨB j)).trans
      (Subgroup.map_subgroupOf_eq_of_le (le_sup_right.trans (hle j)))

theorem conj_eq_commutatorElement_mul {H : Type*} [Group H] (x y : H) :
    x * y * x⁻¹ = ⁅x, y⁆ * y := by
  rw [commutatorElement_def]
  group

section SL3

variable {F : Type*} [Field F]

private theorem h01 : (0 : Fin 3) ≠ 1 := by decide
private theorem h02 : (0 : Fin 3) ≠ 2 := by decide
private theorem h12 : (1 : Fin 3) ≠ 2 := by decide

theorem sl3_conj_tv_one_zero :
    (CFSG.Timmesfeld.tv 0 2 (-1) * CFSG.Timmesfeld.tv 1 0 1 *
      (CFSG.Timmesfeld.tv 0 2 (-1))⁻¹ : SpecialLinearGroup (Fin 3) F) =
      CFSG.Timmesfeld.tv 1 2 1 * CFSG.Timmesfeld.tv 1 0 1 := by
  rw [conj_eq_commutatorElement_mul, ← commutatorElement_inv, CFSG.Timmesfeld.tv_of_ne h01.symm,
    CFSG.Timmesfeld.tv_of_ne h02, CFSG.Timmesfeld.tv_of_ne h12,
    SpecialLinearGroup.commutatorElement_transvection h01.symm h02 h12, one_mul]
  congr 1
  refine inv_eq_of_mul_eq_one_left ?_
  rw [← SpecialLinearGroup.transvection_add, add_neg_cancel,
    SpecialLinearGroup.transvection_coeff_zero]

theorem sl3_conj_tv_zero_one :
    (CFSG.Timmesfeld.tv 2 0 1 * CFSG.Timmesfeld.tv 0 1 1 *
      (CFSG.Timmesfeld.tv 2 0 1)⁻¹ : SpecialLinearGroup (Fin 3) F) =
      CFSG.Timmesfeld.tv 2 1 1 * CFSG.Timmesfeld.tv 0 1 1 := by
  rw [conj_eq_commutatorElement_mul, CFSG.Timmesfeld.tv_of_ne h02.symm,
    CFSG.Timmesfeld.tv_of_ne h01, CFSG.Timmesfeld.tv_of_ne h12.symm,
    SpecialLinearGroup.commutatorElement_transvection h02.symm h01 h12.symm, mul_one]

theorem sl3_conj_tv_two_one :
    (CFSG.Timmesfeld.tv 0 2 1 * CFSG.Timmesfeld.tv 2 1 1 *
      (CFSG.Timmesfeld.tv 0 2 1)⁻¹ : SpecialLinearGroup (Fin 3) F) =
      CFSG.Timmesfeld.tv 0 1 1 * CFSG.Timmesfeld.tv 2 1 1 := by
  rw [conj_eq_commutatorElement_mul, CFSG.Timmesfeld.tv_of_ne h02,
    CFSG.Timmesfeld.tv_of_ne h12.symm, CFSG.Timmesfeld.tv_of_ne h01,
    SpecialLinearGroup.commutatorElement_transvection h02 h12.symm h01, mul_one]

end SL3

theorem mul_mem_of_isConfig_adj [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) {r : ℕ}
    {adj : Fin r → Fin r → Prop} {A B : Fin r → Subgroup G} (hX : IsConfig R adj A B)
    {par : Fin r → Fin r} {dep : Fin r → ℕ} {k₀ : Fin r} (hT : IsRootedTree adj par dep k₀)
    {D : Set G} (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D) {i j : Fin r} (hij : adj i j)
    {ai bi aj bj : G} (hai : A i = Subgroup.zpowers ai) (hbi : B i = Subgroup.zpowers bi)
    (haj : A j = Subgroup.zpowers aj) (hbj : B j = Subgroup.zpowers bj) (hai' : ai ∈ D)
    (hbi' : bi ∈ D) (hbj' : bj ∈ D) :
    aj * bi ∈ D ∧ bj * ai ∈ D ∧ ai * bj ∈ D := by
  obtain ⟨n, -, -, ρ, hρ, hedge⟩ := hX.exists_frame hR hiso hT
  obtain ⟨ψ, hψ⟩ := hedge i j hij
  set F := GaloisField 2 n
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hup : ∀ (k : Fin r) {x : G}, A k = Subgroup.zpowers x →
      ρ k (CFSG.Timmesfeld.tv 0 1 (1 : F)) = x := by
    intro k x hx
    have hmem := Set.mem_range_self (f := fun t => ρ k (CFSG.Timmesfeld.tv 0 1 (t : F))) 1
    rw [Linear.range_tv_upper, (hρ k).2.1, SetLike.mem_coe, hx] at hmem
    refine eq_of_mem_zpowers (mul_self_and_ne_one_of_mem hR (hX.memA k) hx).1 hmem fun h => ?_
    have h' := (hρ k).1 (h.trans (map_one (ρ k)).symm)
    rw [CFSG.Timmesfeld.tv_of_ne h10.symm, ← SpecialLinearGroup.transvection_coeff_zero
      h10.symm] at h'
    exact one_ne_zero (SpecialLinearGroup.transvection_injective h10.symm h')
  have hlow : ∀ (k : Fin r) {x : G}, B k = Subgroup.zpowers x →
      ρ k (CFSG.Timmesfeld.tv 1 0 (1 : F)) = x := by
    intro k x hx
    have hmem := Set.mem_range_self (f := fun t => ρ k (CFSG.Timmesfeld.tv 1 0 (t : F))) 1
    rw [Linear.range_tv_lower, (hρ k).2.2, SetLike.mem_coe, hx] at hmem
    refine eq_of_mem_zpowers (mul_self_and_ne_one_of_mem hR (hX.memB k) hx).1 hmem fun h => ?_
    have h' := (hρ k).1 (h.trans (map_one (ρ k)).symm)
    rw [CFSG.Timmesfeld.tv_of_ne h10, ← SpecialLinearGroup.transvection_coeff_zero h10] at h'
    exact one_ne_zero (SpecialLinearGroup.transvection_injective h10 h')
  obtain ⟨e1, e2, e3, e4⟩ := hψ 1
  rw [hup i hai] at e1
  rw [hlow i hbi] at e2
  rw [hup j haj] at e3
  rw [hlow j hbj] at e4
  refine ⟨?_, ?_, ?_⟩
  · rw [← e3, ← e2, ← map_mul, ← sl3_conj_tv_one_zero, map_mul, map_mul, map_inv, e2]
    exact hDc _ _ hbi'
  · rw [← e4, ← e1, ← map_mul, ← sl3_conj_tv_zero_one, map_mul, map_mul, map_inv, e1]
    exact hDc _ _ hai'
  · rw [← e1, ← e4, ← map_mul, ← sl3_conj_tv_two_one, map_mul, map_mul, map_inv, e4]
    exact hDc _ _ hbj'

end CFSG.LargeExtraspecial.A2Mod
