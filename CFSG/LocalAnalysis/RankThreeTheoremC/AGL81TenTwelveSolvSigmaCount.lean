module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTwelveSolvSigmaDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroSubnormalCommute
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma

open CFSG.Open CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped Pointwise

theorem pCoreOf_le_of_isSylowOf_of_le {Y : Type*} [Group Y] [Finite Y]
    {p : ℕ} [Fact p.Prime] {S L K : Subgroup Y}
    (hS : CFSG.ABGLocalTools.IsSylowOf p S K) (hSL : S ≤ L) (hLK : L ≤ K) :
    pCoreOf p L ≤ S := by
  have hSL' : CFSG.ABGLocalTools.IsSylowOf p S L := hS.of_le hSL hLK
  obtain ⟨Q, hQ⟩ := hSL'.exists_sylow_eq_subgroupOf
  have hcore : CFSG.pCore p ↥L ≤ (Q : Subgroup ↥L) := by
    haveI : (CFSG.pCore p ↥L).Normal := CFSG.pCore_normal
    exact CFSG.pCore_isPGroup.le_sylow_of_normal Q
  have hmap := Subgroup.map_mono (f := L.subtype) hcore
  rw [hQ, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSL] at hmap
  exact hmap

theorem conjAct_smul_eq_map_conj {Y : Type*} [Group Y] (g : Y) (J : Subgroup Y) :
    ConjAct.toConjAct g • J = J.map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  rfl

theorem conjAct_subgroup_smul_eq_map_conj {Y : Type*} [Group Y]
    (Y₀ J : Subgroup Y) (y : Y₀) :
    letI : MulAction Y₀ (Subgroup Y) :=
      MulAction.compHom (Subgroup Y)
        ((ConjAct.toConjAct : Y ≃* ConjAct Y).toMonoidHom.comp Y₀.subtype)
    y • J = J.map (MulAut.conj (y : Y)).toMonoidHom := by
  letI : MulAction Y₀ (Subgroup Y) :=
    MulAction.compHom (Subgroup Y)
      ((ConjAct.toConjAct : Y ≃* ConjAct Y).toMonoidHom.comp Y₀.subtype)
  rw [MulAction.compHom_smul_def]
  change ConjAct.toConjAct (y : Y) • J = J.map (MulAut.conj (y : Y)).toMonoidHom
  rw [conjAct_smul_eq_map_conj]

theorem stabilizer_conj_eq_normalizer {Y : Type*} [Group Y] (Y₀ J : Subgroup Y) :
    letI : MulAction Y₀ (Subgroup Y) :=
      MulAction.compHom (Subgroup Y)
        ((ConjAct.toConjAct : Y ≃* ConjAct Y).toMonoidHom.comp Y₀.subtype)
    MulAction.stabilizer Y₀ J =
      (Subgroup.normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀ := by
  letI : MulAction Y₀ (Subgroup Y) :=
    MulAction.compHom (Subgroup Y)
      ((ConjAct.toConjAct : Y ≃* ConjAct Y).toMonoidHom.comp Y₀.subtype)
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  change ConjAct.toConjAct (y : Y) • J = J ↔
    (y : Y) ∈ Subgroup.normalizer (J : Set Y) ∧ (y : Y) ∈ Y₀
  rw [Subgroup.conjAct_pointwise_smul_iff]
  simp [y.2]

theorem orbit_eq_three {H X : Type*} [Group H] [MulAction H X] [Finite X]
    {a : X} {y : H} (hcard : (MulAction.orbit H a).ncard = 3)
    (h1 : y • a ≠ a) (h2 : y ^ 2 • a ≠ a) (h12 : y ^ 2 • a ≠ y • a) :
    MulAction.orbit H a = {a, y • a, y ^ 2 • a} := by
  classical
  let S : Finset X := {a, y • a, y ^ 2 • a}
  have hS : S.card = 3 := by
    have h₁ : a ∉ ({y • a, y ^ 2 • a} : Finset X) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h1.symm, h2.symm⟩
    have h₂ : y • a ∉ ({y ^ 2 • a} : Finset X) := by
      simp only [Finset.mem_singleton]
      exact h12.symm
    rw [show S = insert a (insert (y • a) {y ^ 2 • a}) from rfl,
      Finset.card_insert_of_notMem h₁, Finset.card_insert_of_notMem h₂,
      Finset.card_singleton]
  have hsub : (S : Set X) ⊆ MulAction.orbit H a := by
    intro x hx
    simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    · rw [h]; exact MulAction.mem_orbit_self a
    · rw [h]; exact MulAction.mem_orbit_iff.mpr ⟨y, rfl⟩
    · rw [h]; exact MulAction.mem_orbit_iff.mpr ⟨y ^ 2, rfl⟩
  have hEq : (S : Set X) = MulAction.orbit H a := by
    apply Set.eq_of_subset_of_ncard_le hsub
    rw [hcard, Set.ncard_coe_finset, hS]
  simpa [S] using hEq.symm

theorem index_normalizer_ge_three {Y : Type*} [Group Y] [Finite Y]
    (Y₀ J : Subgroup Y) {g₁ g₂ : Y} (hg₁ : g₁ ∈ Y₀) (hg₂ : g₂ ∈ Y₀)
    (h1 : J.map (MulAut.conj g₁).toMonoidHom ≠ J)
    (h2 : J.map (MulAut.conj g₂).toMonoidHom ≠ J)
    (h12 : J.map (MulAut.conj g₂).toMonoidHom ≠
      J.map (MulAut.conj g₁).toMonoidHom) :
    3 ≤ ((Subgroup.normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀).index := by
  classical
  let act : MulAction Y₀ (Subgroup Y) :=
    MulAction.compHom (Subgroup Y)
      ((ConjAct.toConjAct : Y ≃* ConjAct Y).toMonoidHom.comp Y₀.subtype)
  letI := act
  have hstab_index : (MulAction.stabilizer Y₀ J).index =
      (MulAction.orbit Y₀ J).ncard :=
    @MulAction.index_stabilizer Y₀ (Subgroup Y) _ act J
  let J₁ : Subgroup Y := J.map (MulAut.conj g₁).toMonoidHom
  let J₂ : Subgroup Y := J.map (MulAut.conj g₂).toMonoidHom
  let S : Finset (Subgroup Y) := {J, J₁, J₂}
  have hJ : J ∉ ({J₁, J₂} : Finset (Subgroup Y)) := by
    simp only [J₁, J₂, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1.symm, h2.symm⟩
  have hJ1 : J₁ ∉ ({J₂} : Finset (Subgroup Y)) := by
    simp only [J₁, J₂, Finset.mem_singleton]
    exact h12.symm
  have hS : S.card = 3 := by
    rw [show S = insert J (insert J₁ {J₂}) from rfl,
      Finset.card_insert_of_notMem hJ, Finset.card_insert_of_notMem hJ1,
      Finset.card_singleton]
  have hsub : (S : Set (Subgroup Y)) ⊆ MulAction.orbit Y₀ J := by
    intro K hK
    simp only [S, J₁, J₂, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hK
    rcases hK with h | h | h
    · rw [h]
      exact MulAction.mem_orbit_self J
    · rw [h]
      refine MulAction.mem_orbit_iff.mpr ⟨⟨g₁, hg₁⟩, ?_⟩
      rw [conjAct_subgroup_smul_eq_map_conj]
    · rw [h]
      refine MulAction.mem_orbit_iff.mpr ⟨⟨g₂, hg₂⟩, ?_⟩
      rw [conjAct_subgroup_smul_eq_map_conj]
  have hle : S.card ≤ (MulAction.orbit Y₀ J).ncard := by
    rw [← Set.ncard_coe_finset S]
    exact Set.ncard_le_ncard hsub
  calc
    3 = S.card := hS.symm
    _ ≤ (MulAction.orbit Y₀ J).ncard := hle
    _ = (MulAction.stabilizer Y₀ J).index := hstab_index.symm
    _ = ((Subgroup.normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀).index := by
        congr 1
        exact stabilizer_conj_eq_normalizer Y₀ J

theorem iSup_eq_of_range_eq_three {ι α : Type*} [CompleteLattice α]
    {s : Set ι} {f : ι → α} {a b c : α}
    (h : ∀ i, i ∈ s → f i = a ∨ f i = b ∨ f i = c)
    (ha : ∃ i, i ∈ s ∧ f i = a) (hb : ∃ i, i ∈ s ∧ f i = b)
    (hc : ∃ i, i ∈ s ∧ f i = c) :
    (⨆ i, ⨆ (_ : i ∈ s), f i) = a ⊔ b ⊔ c := by
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun hi => ?_
    rcases h i hi with h | h | h
    · rw [h]
      exact le_sup_left.trans le_sup_left
    · rw [h]
      exact le_sup_right.trans le_sup_left
    · rw [h]
      exact le_sup_right
  · refine sup_le (sup_le ?_ ?_) ?_
    · obtain ⟨i, hi, hfi⟩ := ha
      rw [← hfi]
      exact le_biSup f hi
    · obtain ⟨i, hi, hfi⟩ := hb
      rw [← hfi]
      exact le_biSup f hi
    · obtain ⟨i, hi, hfi⟩ := hc
      rw [← hfi]
      exact le_biSup f hi

theorem exists_three_elt_not_mem_normalizer {Y : Type} [Group Y] [Finite Y]
    {K Y₀ J : Subgroup Y} (hKn : K.Normal) (hK : SolvSigmaSylowFacts ↥K) (S : Sylow 3 ↥K)
    (hSY : (S : Subgroup ↥K).map K.subtype ≤ Y₀)
    (hγ : ∀ A : Subgroup ↥K, A ≤ S → IsElemAbelian 3 A → Nat.card A = 27 →
      normalizer ((A.map K.subtype : Subgroup Y) : Set Y) ≤ Y₀)
    (hJK : J ≤ K) (hJ3 : IsPGroup 3 J) (hJne : J ≠ ⊥) (hJsub : IsSubnormal J (K ⊓ Y₀))
    (hdir : SolvThreeDirectCond Y₀ J)
    (htype : (∀ a ∈ J, ∀ b ∈ J, a * b = b * a) → Nat.card J = 3) :
    Nat.card J = 3 ∧ ∃ y ∈ Y₀, (∃ k : ℕ, y ^ 3 ^ k = 1) ∧ y ∉ normalizer (J : Set Y) ∧
      Nat.card ↥(J ⊔ J.map (MulAut.conj y).toMonoidHom ⊔
        J.map (MulAut.conj (y ^ 2)).toMonoidHom) = 27 := by
  classical
  haveI : K.Normal := hKn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hAS, hAe, hA27, hδ1, hδ2⟩ := hK S
  let Abar : Subgroup Y := A.map K.subtype
  have hAbar_le_K : Abar ≤ K := Subgroup.map_subtype_le _
  have hAbar_le_Y₀ : Abar ≤ Y₀ := (Subgroup.map_mono hAS).trans hSY
  have hAbar_e : IsElemAbelian 3 Abar := hAe.map K.subtype
  have hAbar_card : Nat.card Abar = 27 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hA27]
  let T : Subgroup Y := K ⊓ Y₀
  have hAbar_le_T : Abar ≤ T := le_inf hAbar_le_K hAbar_le_Y₀
  have hN_Abar_le_Y₀ : Subgroup.normalizer (Abar : Set Y) ≤ Y₀ := hγ A hAS hAe hA27
  have hNK_le_Y₀ : ∀ g ∈ Subgroup.normalizer (A : Set ↥K), (g : Y) ∈ Y₀ := by
    intro g hg
    exact hN_Abar_le_Y₀
      (Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩))
  let Sbar : Subgroup Y := (S : Subgroup ↥K).map K.subtype
  have hSbar_le_K : Sbar ≤ K := Subgroup.map_subtype_le _
  have hSbar_le_T : Sbar ≤ T := le_inf hSbar_le_K hSY
  have hSylK : CFSG.ABGLocalTools.IsSylowOf 3 Sbar K := ⟨S, rfl⟩
  have hcoreS : pCoreOf 3 T ≤ Sbar :=
    pCoreOf_le_of_isSylowOf_of_le hSylK hSbar_le_T inf_le_left
  have hY0T : Y₀ ≤ Subgroup.normalizer (T : Set Y) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hyY : Y₀.map (MulAut.conj y) = Y₀ := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact Y₀.mul_mem (Y₀.mul_mem hy hw) (Y₀.inv_mem hy)
      · intro hz
        refine ⟨y⁻¹ * z * y, Y₀.mul_mem (Y₀.mul_mem (Y₀.inv_mem hy) hz) hy, ?_⟩
        show y * (y⁻¹ * z * y) * y⁻¹ = z
        group
    calc T.map (MulAut.conj y) = (K.map (MulAut.conj y)) ⊓ (Y₀.map (MulAut.conj y)) := by
          dsimp [T]
          rw [Subgroup.map_inf _ _ _ (MulAut.conj y).injective]
      _ = K ⊓ Y₀ := by
          have hKconj : K.map (MulAut.conj y) = K :=
            Subgroup.Normal.map_conj_eq (H := K) y
          rw [hKconj, hyY]
      _ = T := rfl
  have hY0O : Y₀ ≤ Subgroup.normalizer (pCoreOf 3 T : Set Y) :=
    hY0T.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 3 T)
  have hcoreT : pCoreOf 3 T ≤ Abar := by
    intro r hr
    by_contra hrA
    have hrS : r ∈ Sbar := hcoreS hr
    obtain ⟨s, hsS, hsr⟩ := Subgroup.mem_map.mp hrS
    have hsA : s ∉ A := by
      intro hsA
      exact hrA (by rw [← hsr]; exact Subgroup.mem_map_of_mem K.subtype hsA)
    obtain ⟨g, hgN, hgconj⟩ := hδ1 s hsS hsA
    have hgY : (g : Y) ∈ Y₀ := hNK_le_Y₀ g hgN
    have hconj_mem : (g : Y) * r * (g : Y)⁻¹ ∈ pCoreOf 3 T :=
      (Subgroup.mem_normalizer_iff.mp (hY0O hgY) r).mp hr
    have hconj_eq : (g : Y) * r * (g : Y)⁻¹ = K.subtype (g * s * g⁻¹) := by
      rw [← hsr]
      simp [map_mul]
    have hnotSbar : K.subtype (g * s * g⁻¹) ∉ Sbar := by
      intro hmem
      obtain ⟨t, htS, hteq⟩ := Subgroup.mem_map.mp hmem
      exact hgconj (by rwa [K.subtype_injective hteq] at htS)
    exact hnotSbar (hconj_eq ▸ hcoreS hconj_mem)
  have hJ_le_O : J ≤ pCoreOf 3 T :=
    CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal hJsub hJ3
  have hJ_le_Abar : J ≤ Abar := hJ_le_O.trans hcoreT
  have hJcomm : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a := by
    haveI : IsMulCommutative ↥Abar := hAbar_e.1
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm' (⟨a, hJ_le_Abar ha⟩ : Abar) ⟨b, hJ_le_Abar hb⟩)
  have hJcard : Nat.card J = 3 := htype hJcomm
  let Jc : Y → Subgroup Y := fun z => J.map (MulAut.conj z)
  let D : Subgroup Y := ⨆ y ∈ Y₀, Jc y
  have hD_le_Abar : D ≤ Abar := by
    dsimp [D]
    refine iSup_le fun y => iSup_le fun hy => ?_
    have hyO : (pCoreOf 3 T).map (MulAut.conj y) = pCoreOf 3 T :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hY0O hy)
    have hconj : Jc y ≤ pCoreOf 3 T := by
      have := Subgroup.map_mono (f := (MulAut.conj y : Y →* Y)) hJ_le_O
      rwa [hyO] at this
    exact hconj.trans hcoreT
  have hD3 : IsPGroup 3 D := hAbar_e.isPGroup.to_le hD_le_Abar
  have hO2D : CFSG.pCore 2 ↥D = ⊥ := by
    have h2 : IsPGroup 2 (CFSG.pCore 2 ↥D) := CFSG.pCore_isPGroup
    have h3 : IsPGroup 3 (⊤ : Subgroup ↥D) := hD3.of_equiv Subgroup.topEquiv.symm
    rw [eq_bot_iff]
    intro x hx
    exact (IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ h2 h3).le_bot
      ⟨hx, Subgroup.mem_top _⟩
  have hO2J : CFSG.pCore 2 ↥J = ⊥ := by
    have h2 : IsPGroup 2 (CFSG.pCore 2 ↥J) := CFSG.pCore_isPGroup
    have h3 : IsPGroup 3 (⊤ : Subgroup ↥J) := hJ3.of_equiv Subgroup.topEquiv.symm
    rw [eq_bot_iff]
    intro x hx
    exact (IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ h2 h3).le_bot
      ⟨hx, Subgroup.mem_top _⟩
  set h : ℕ := ((Subgroup.normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀).index with hh
  have hdir' : Nat.card D = Nat.card J ^ h := by
    have hd := hdir
    dsimp [SolvThreeDirectCond] at hd
    rw [← hh] at hd
    change Nat.card (↥D ⧸ CFSG.pCore 2 ↥D) =
      Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) ^ h at hd
    rw [hO2D, hO2J,
      Nat.card_congr (QuotientGroup.quotientBot (G := ↥D)).toEquiv,
      Nat.card_congr (QuotientGroup.quotientBot (G := ↥J)).toEquiv] at hd
    exact hd
  have hD_dvd : Nat.card D ∣ 27 :=
    (Subgroup.card_dvd_of_le hD_le_Abar).trans (by rw [hAbar_card])
  have hpow_dvd : 3 ^ h ∣ 27 := by
    have h := hD_dvd
    rw [hdir', hJcard] at h
    exact h
  have hle3 : h ≤ 3 := by
    have hle : 3 ^ h ≤ 3 ^ 3 := Nat.le_of_dvd (by norm_num) hpow_dvd
    exact (pow_le_pow_iff_right₀ (by norm_num : 1 < 3)).mp (by simpa using hle)
  haveI : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).mpr hJne
  obtain ⟨x, hxJ, hx1⟩ := Subgroup.exists_ne_one_of_nontrivial J
  have hxmap : x ∈ Abar := hJ_le_Abar hxJ
  obtain ⟨a, haA, hax⟩ := Subgroup.mem_map.mp hxmap
  have ha1 : a ≠ 1 := by
    intro h
    apply hx1
    rw [← hax, h, map_one]
  have hJz : J = Subgroup.zpowers (K.subtype a) := by
    have hx3 : orderOf x = 3 := by
      have hdvd : orderOf x ∣ 3 := by
        simpa [hJcard] using Subgroup.orderOf_dvd_natCard J hxJ
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    have hx_eq : x = K.subtype a := hax.symm
    have hJx : J = Subgroup.zpowers x := by
      symm
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxJ)
      rw [Nat.card_zpowers, hx3, hJcard]
    rw [hJx, hx_eq]
  obtain ⟨g₁, hg₁N, g₂, hg₂N, hg₁a, hg₂a, hg₂g₁⟩ := hδ2 a haA ha1
  have hg₁Y : (g₁ : Y) ∈ Y₀ := hNK_le_Y₀ g₁ hg₁N
  have hg₂Y : (g₂ : Y) ∈ Y₀ := hNK_le_Y₀ g₂ hg₂N
  have hmap_zpowers (g : ↥K) :
      J.map (MulAut.conj (g : Y)).toMonoidHom =
        Subgroup.zpowers (K.subtype (g * a * g⁻¹)) := by
    rw [hJz, MonoidHom.map_zpowers]
    simp [map_mul]
  have h1 : J.map (MulAut.conj (g₁ : Y)).toMonoidHom ≠ J := by
    intro heq
    have hmem : K.subtype (g₁ * a * g₁⁻¹) ∈
        J.map (MulAut.conj (g₁ : Y)).toMonoidHom := by
      rw [hmap_zpowers g₁]
      exact Subgroup.mem_zpowers _
    rw [heq, hJz, ← MonoidHom.map_zpowers] at hmem
    obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.mp hmem
    have hk' : k = g₁ * a * g₁⁻¹ := K.subtype_injective hkeq
    exact hg₁a (by simpa [hk'] using hk)
  have h2 : J.map (MulAut.conj (g₂ : Y)).toMonoidHom ≠ J := by
    intro heq
    have hmem : K.subtype (g₂ * a * g₂⁻¹) ∈
        J.map (MulAut.conj (g₂ : Y)).toMonoidHom := by
      rw [hmap_zpowers g₂]
      exact Subgroup.mem_zpowers _
    rw [heq, hJz, ← MonoidHom.map_zpowers] at hmem
    obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.mp hmem
    have hk' : k = g₂ * a * g₂⁻¹ := K.subtype_injective hkeq
    exact hg₂a (by simpa [hk'] using hk)
  have h12 : J.map (MulAut.conj (g₂ : Y)).toMonoidHom ≠
      J.map (MulAut.conj (g₁ : Y)).toMonoidHom := by
    intro heq
    have hmem : K.subtype (g₂ * a * g₂⁻¹) ∈
        J.map (MulAut.conj (g₂ : Y)).toMonoidHom := by
      rw [hmap_zpowers g₂]
      exact Subgroup.mem_zpowers _
    rw [heq, hmap_zpowers g₁, ← MonoidHom.map_zpowers] at hmem
    obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.mp hmem
    have hk' : k = g₂ * a * g₂⁻¹ := K.subtype_injective hkeq
    exact hg₂g₁ (by simpa [hk'] using hk)
  have hge3 : 3 ≤ h := by
    rw [hh]
    exact index_normalizer_ge_three Y₀ J hg₁Y hg₂Y h1 h2 h12
  have h_eq_three : h = 3 := le_antisymm hle3 hge3
  let H : Subgroup ↥Y₀ := (Subgroup.normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀
  have hH_index : H.index = 3 := by
    rw [← hh, h_eq_three]
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 ↥Y₀))
  have hPnotle : ¬ (P : Subgroup ↥Y₀) ≤ H := by
    intro hle
    have hdvd : H.index ∣ (P : Subgroup ↥Y₀).index := Subgroup.index_dvd_of_le hle
    have h3dvd : 3 ∣ H.index := by rw [hH_index]
    exact P.not_dvd_index (h3dvd.trans hdvd)
  obtain ⟨y, hyP, hyH⟩ := Set.not_subset.mp (show ¬ (P : Set ↥Y₀) ⊆ (H : Set ↥Y₀) from hPnotle)
  have hyY₀ : (y : Y) ∈ Y₀ := y.2
  have hy3 : ∃ k : ℕ, (y : Y) ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := P.isPGroup' (⟨y, hyP⟩ : ↥(P : Subgroup ↥Y₀))
    have hk' := congrArg (fun z : ↥(P : Subgroup ↥Y₀) => ((z : ↥Y₀) : Y)) hk
    exact ⟨k, by simpa using hk'⟩
  have hyN : (y : Y) ∉ Subgroup.normalizer (J : Set Y) := by
    intro hyN
    apply hyH
    change y ∈ (Subgroup.normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨hyN, hyY₀⟩
  have hyJ : J.map (MulAut.conj (y : Y)).toMonoidHom ≠ J := by
    intro heq
    exact hyN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa using heq))
  have hy_odd : Odd (orderOf (y : Y)) := by
    obtain ⟨k, hk⟩ := hy3
    exact Odd.of_dvd_nat (Odd.pow (by norm_num : Odd 3)) (orderOf_dvd_of_pow_eq_one hk)
  have hy2J : J.map (MulAut.conj ((y : Y) ^ 2)).toMonoidHom ≠ J := by
    intro heq
    have hy2N : (y : Y) ^ 2 ∈ Subgroup.normalizer (J : Set Y) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa using heq)
    have hy_mem : (y : Y) ∈ Subgroup.zpowers ((y : Y) ^ 2) := by
      rw [mem_zpowers_pow_iff]
      exact Odd.coprime_two_left hy_odd
    exact hyN ((Subgroup.zpowers_le.mpr hy2N) hy_mem)
  have h2yJ : J.map (MulAut.conj ((y : Y) ^ 2)).toMonoidHom ≠
      J.map (MulAut.conj (y : Y)).toMonoidHom := by
    intro heq
    have hfix : J.map (MulAut.conj (y : Y)).toMonoidHom = J := by
      have h := congrArg
        (fun K : Subgroup Y => K.map (MulAut.conj ((y : Y)⁻¹)).toMonoidHom) heq
      have hcomp1 : ((MulAut.conj ((y : Y)⁻¹)).toMonoidHom.comp
          (MulAut.conj ((y : Y) ^ 2)).toMonoidHom) =
          (MulAut.conj (y : Y)).toMonoidHom := by
        ext z
        simp [MulAut.conj_apply, pow_two, mul_assoc]
      have hcomp2 : ((MulAut.conj ((y : Y)⁻¹)).toMonoidHom.comp
          (MulAut.conj (y : Y)).toMonoidHom) = MonoidHom.id Y := by
        ext z
        simp [MulAut.conj_apply, pow_two, mul_assoc]
      rw [Subgroup.map_map, Subgroup.map_map, hcomp1, hcomp2, Subgroup.map_id] at h
      exact h
    exact hyN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfix)
  let act : MulAction Y₀ (Subgroup Y) :=
    MulAction.compHom (Subgroup Y)
      ((ConjAct.toConjAct : Y ≃* ConjAct Y).toMonoidHom.comp Y₀.subtype)
  letI := act
  have hstab : MulAction.stabilizer Y₀ J = H := by
    change MulAction.stabilizer Y₀ J =
      (Subgroup.normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀
    exact stabilizer_conj_eq_normalizer Y₀ J
  have hstab_index : (MulAction.stabilizer Y₀ J).index =
      (MulAction.orbit Y₀ J).ncard :=
    @MulAction.index_stabilizer Y₀ (Subgroup Y) _ act J
  have horbit_card : (MulAction.orbit Y₀ J).ncard = 3 := by
    rw [← hstab_index, hstab, hH_index]
  have hyY0 : (⟨(y : Y), hyY₀⟩ : Y₀) = y := by ext; rfl
  have horbit_eq : MulAction.orbit Y₀ J =
      {J, (y : Y₀) • J, ((y : Y₀) ^ 2) • J} := by
    apply orbit_eq_three horbit_card
    · rw [conjAct_subgroup_smul_eq_map_conj]
      exact hyJ
    · rw [conjAct_subgroup_smul_eq_map_conj]
      exact hy2J
    · rw [conjAct_subgroup_smul_eq_map_conj, conjAct_subgroup_smul_eq_map_conj]
      exact h2yJ
  let J1 : Subgroup Y := Jc (y : Y)
  let J2 : Subgroup Y := Jc ((y : Y) ^ 2)
  have hD_eq : D = J ⊔ J1 ⊔ J2 := by
    have hrange : ∀ z : Y, z ∈ Y₀ → J.map (MulAut.conj z) = J ∨
        J.map (MulAut.conj z) = (y : Y₀) • J ∨
        J.map (MulAut.conj z) = ((y : Y₀) ^ 2) • J := by
      intro z hz
      have hmem : (⟨z, hz⟩ : Y₀) • J ∈ MulAction.orbit Y₀ J :=
        MulAction.mem_orbit_iff.mpr ⟨⟨z, hz⟩, rfl⟩
      rw [horbit_eq] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rw [conjAct_subgroup_smul_eq_map_conj] at hmem
      exact hmem
    have h := iSup_eq_of_range_eq_three
      (s := (Y₀ : Set Y)) (f := fun z : Y => J.map (MulAut.conj z))
      (a := J) (b := (y : Y₀) • J) (c := ((y : Y₀) ^ 2) • J)
      hrange ⟨1, one_mem Y₀, by simp [MulAut.one_def, Subgroup.map_id]⟩
        ⟨(y : Y), y.2, by
          rw [conjAct_subgroup_smul_eq_map_conj]
          rfl⟩
        ⟨((y : Y) ^ 2), Y₀.pow_mem y.2 2, by
          rw [conjAct_subgroup_smul_eq_map_conj]
          rfl⟩
    calc
      D = (⨆ z : Y, ⨆ (_ : z ∈ (Y₀ : Set Y)), J.map (MulAut.conj z)) := rfl
      _ = J ⊔ (y : Y₀) • J ⊔ ((y : Y₀) ^ 2) • J := h
      _ = J ⊔ J1 ⊔ J2 := by
        rw [conjAct_subgroup_smul_eq_map_conj, conjAct_subgroup_smul_eq_map_conj]
        dsimp [J1, J2, Jc]
  refine ⟨hJcard, y, hyY₀, hy3, hyN, ?_⟩
  have hcardD : Nat.card D = 27 := by
    rw [hdir', h_eq_three, hJcard]
    norm_num
  change Nat.card ↥(J ⊔ J1 ⊔ J2) = 27
  rw [← hD_eq]
  exact hcardD

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma
