module

public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideBlocks

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

@[expose] def StmtJ3MSide : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G},
    D1J3Data P M H R → CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥

section J3MSide

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}

omit [Finite G] in
private theorem exists_pow_mem_of_mem_sup_of_le_normalizer {p : ℕ} {V C : Subgroup G}
    (hV : IsPGroup p V) (hVC : V ≤ Subgroup.normalizer (C : Set G)) {u : G} (hu : u ∈ V ⊔ C) :
    ∃ e : ℕ, u ^ p ^ e ∈ C := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right V C hVC] at hu
  obtain ⟨v, hv, c, hc, rfl⟩ := hu
  obtain ⟨e, he⟩ := hV ⟨v, hv⟩
  have hve : v ^ p ^ e = 1 := by simpa using congrArg Subtype.val he
  have key : ∀ n : ℕ, ∃ c' ∈ C, (v * c) ^ n = v ^ n * c' := by
    intro n
    induction n with
    | zero => exact ⟨1, C.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨c', hc', hn⟩ := ih
      refine ⟨v⁻¹ * c' * v * c, C.mul_mem ?_ hc, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hVC (V.inv_mem hv)) c').mp hc'
        simpa using this
      · rw [pow_succ, hn, pow_succ]
        group
  obtain ⟨c', hc', hn⟩ := key (p ^ e)
  exact ⟨e, by rw [hn, hve, one_mul]; exact hc'⟩

theorem D1J3Data.commutator_mem_blockCentralizer (h : D1J3Data P M H R) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (hD2 : D1NoXBlock)
    (hBlk : KFactBlockThreeSolvable) (hb : StmtBlockInnerNormalizer) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {a b : G} (ha : a ∈ R ⊓ (L ⊔ blockCentralizer M L))
    (hb' : b ∈ R ⊓ (L ⊔ blockCentralizer M L)) :
    a * b * a⁻¹ * b⁻¹ ∈ blockCentralizer M L := by
  have h3 := h.surv.ph3
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  set S := pCoreOf 2 H with hSdef
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLbdef
  set Cb := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  have hLM : L ≤ M := hL.le
  have hbarC : barM M (blockCentralizer M L) ≤ Cb := by
    rintro _ ⟨⟨c, hcM⟩, hc, rfl⟩
    exact (mem_blockCentralizer_iff ⟨c, hcM⟩).mp (Subgroup.mem_subgroupOf.mp hc)
  have hCL : blockCentralizer M L ≤ Subgroup.normalizer (L : Set G) :=
    hL.toIsTwoPrimeComponent.le_normalizer (hbarC.trans (Subgroup.centralizer_le_normalizer _))
      (blockCentralizer_le M L)
  have hRLN : R ⊓ (L ⊔ blockCentralizer M L) ≤ Subgroup.normalizer (L : Set G) :=
    inf_le_right.trans (sup_le Subgroup.le_normalizer hCL)
  have hNC : Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have hbarN : ∀ x : M, (x : G) ∈ Subgroup.normalizer (L : Set G) →
      mk x ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro x hx
    have hL' : L.map (MulAut.conj (x : G)).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
    have hLbar : (barM M L).map (MulAut.conj (mk x)).toMonoidHom = barM M L := by
      rw [← barM_map_conj x.2, hL']
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hLbar
  have hSL : barM M S ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    h86 G M S h3.isKGroup.1 h3.asc81bHyp _ hL.component
  have act : ∀ g l : ↥M ⧸ CFSG.pCore 2 ↥M, l ∈ Lb → g * l⁻¹ ∈ Cb →
      ∀ y ∈ Lb, g * y * g⁻¹ = l * y * l⁻¹ := by
    intro g l hl hgl y hy
    have hly : l * y * l⁻¹ ∈ Lb := Lb.mul_mem (Lb.mul_mem hl hy) (Lb.inv_mem hl)
    have hz := Subgroup.mem_centralizer_iff.mp hgl _ hly
    calc g * y * g⁻¹ = (g * l⁻¹) * (l * y * l⁻¹) * (g * l⁻¹)⁻¹ := by group
      _ = (l * y * l⁻¹) * (g * l⁻¹) * (g * l⁻¹)⁻¹ := by rw [← hz]
      _ = l * y * l⁻¹ := by group
  have actInv : ∀ g l : ↥M ⧸ CFSG.pCore 2 ↥M, l ∈ Lb → g * l⁻¹ ∈ Cb →
      ∀ y ∈ Lb, g⁻¹ * y * g = l⁻¹ * y * l := by
    intro g l hl hgl y hy
    have hy' : l⁻¹ * y * l ∈ Lb := Lb.mul_mem (Lb.mul_mem (Lb.inv_mem hl) hy) hl
    have e := act g l hl hgl _ hy'
    calc g⁻¹ * y * g = g⁻¹ * (l * (l⁻¹ * y * l) * l⁻¹) * g := by group
      _ = g⁻¹ * (g * (l⁻¹ * y * l) * g⁻¹) * g := by rw [e]
      _ = l⁻¹ * y * l := by group
  have decomp : ∀ x ∈ R ⊓ (L ⊔ blockCentralizer M L), ∃ (hxM : x ∈ M) (l : G) (hlL : l ∈ L),
      mk ⟨x, hxM⟩ * (mk ⟨l, hLM hlL⟩)⁻¹ ∈ Cb := by
    intro x hx
    have hxLC : x ∈ ((blockCentralizer M L ⊔ L : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hx.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ L hCL] at hxLC
    obtain ⟨c, hc, l, hl, rfl⟩ := hxLC
    have hcM := blockCentralizer_le M L hc
    refine ⟨M.mul_mem hcM (hLM hl), l, hl, ?_⟩
    have e : mk ⟨c * l, M.mul_mem hcM (hLM hl)⟩ = mk ⟨c, hcM⟩ * mk ⟨l, hLM hl⟩ := by
      rw [← map_mul]
      rfl
    rw [e, mul_inv_cancel_right]
    exact (mem_blockCentralizer_iff ⟨c, hcM⟩).mp hc
  have inP : ∀ x ∈ R ⊓ (L ⊔ blockCentralizer M L), ∀ (hxM : x ∈ M) (l : G) (hlL : l ∈ L),
      mk ⟨x, hxM⟩ * (mk ⟨l, hLM hlL⟩)⁻¹ ∈ Cb →
        mk ⟨l, hLM hlL⟩ ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L) := by
    intro x hx hxM l hlL hxl
    have hlLb : mk ⟨l, hLM hlL⟩ ∈ Lb :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hlL)
    have hxS : x ∈ Subgroup.normalizer (S : Set G) := (hKeq ▸ h3.le_inf hx.1).2
    refine hb h3 h84 h86 hD2 hL _ hlLb fun s hs => ?_
    obtain ⟨⟨σ, hσM⟩, hσ, rfl⟩ := hs
    have hσS : σ ∈ S := Subgroup.mem_subgroupOf.mp hσ
    have hσ' : x * σ * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hxS σ).mp hσS
    refine ⟨mk ⟨x, hxM⟩ * mk ⟨σ, hσM⟩ * (mk ⟨x, hxM⟩)⁻¹, ?_, fun y hy => ?_⟩
    · refine ⟨⟨x, hxM⟩ * ⟨σ, hσM⟩ * (⟨x, hxM⟩)⁻¹, Subgroup.mem_subgroupOf.mpr hσ', ?_⟩
      simp only [map_mul, map_inv]
      rfl
    · set g := mk ⟨x, hxM⟩
      set lb := mk ⟨l, hLM hlL⟩
      set sb := mk ⟨σ, hσM⟩
      have hsb : sb ∈ barM M S := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hσS)
      have hy1 : lb⁻¹ * y * lb ∈ Lb := Lb.mul_mem (Lb.mul_mem (Lb.inv_mem hlLb) hy) hlLb
      have hy2 : sb * (lb⁻¹ * y * lb) * sb⁻¹ ∈ Lb :=
        (Subgroup.mem_normalizer_iff.mp (hSL hsb) _).mp hy1
      have e1 := actInv g lb hlLb hxl y hy
      have e2 := act g lb hlLb hxl _ hy2
      calc lb * sb * lb⁻¹ * y * (lb * sb * lb⁻¹)⁻¹
          = lb * (sb * (lb⁻¹ * y * lb) * sb⁻¹) * lb⁻¹ := by group
        _ = g * (sb * (lb⁻¹ * y * lb) * sb⁻¹) * g⁻¹ := e2.symm
        _ = g * (sb * (g⁻¹ * y * g) * sb⁻¹) * g⁻¹ := by rw [e1]
        _ = g * sb * g⁻¹ * y * (g * sb * g⁻¹)⁻¹ := by group
  set RL := R ⊓ (L ⊔ blockCentralizer M L) with hRLdef
  have hRL3 : IsPGroup 3 (barM M RL) :=
    ((h3.isPGroup_R.to_le inf_le_left).comap_subtype (K := M)).map _
  have hRLC : barM M RL ≤ Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hNC (hbarN x (hRLN (Subgroup.mem_subgroupOf.mp hx)))
  set U := barM M (Subgroup.normalizer (S : Set G) ⊓ L) ⊓ (barM M RL ⊔ Cb) with hUdef
  have hU3 : ∀ u ∈ U, ∃ e : ℕ, u ^ 3 ^ e ∈ Cb := fun u hu =>
    exists_pow_mem_of_mem_sup_of_le_normalizer hRL3 hRLC hu.2
  have inU : ∀ x ∈ RL, ∀ (hxM : x ∈ M) (l : G) (hlL : l ∈ L),
      mk ⟨x, hxM⟩ * (mk ⟨l, hLM hlL⟩)⁻¹ ∈ Cb → mk ⟨l, hLM hlL⟩ ∈ U := by
    intro x hx hxM l hlL hxl
    refine ⟨inP x hx hxM l hlL hxl, ?_⟩
    have e : mk ⟨l, hLM hlL⟩ = (mk ⟨x, hxM⟩ * (mk ⟨l, hLM hlL⟩)⁻¹)⁻¹ * mk ⟨x, hxM⟩ := by group
    rw [e]
    exact (barM M RL ⊔ Cb).mul_mem (Subgroup.mem_sup_right (Cb.inv_mem hxl))
      (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)))
  obtain ⟨hβ, -⟩ := hBlk G M S L (GLBPrimeCore 3 H) (R ⊔ GLBPrimeCore 3 H) h3.isKGroup.1
    h3.asc81bHyp hL (h3.nineThree_not_one h85 hD2 hL).1 (h3.not_isSylowTwoOf_inf h85 hD2 hL)
    le_sup_right (hKeq ▸ sup_le h3.le_inf (le_inf (glbPrimeCore_le 3 H) h3.primeCore_le))
    (hKeq ▸ (inf_le_left.trans (le_normalizer_glbPrimeCore 3 H))) (hKeq ▸ h.normal_sup)
    (glbPrimeCore_coprime 3 H)
    (fun x hx => exists_pow_mem_of_mem_sup_of_le_normalizer h3.isPGroup_R
      (h3.le_H.trans (le_normalizer_glbPrimeCore 3 H)) hx)
    (fun k hk => h.two_top k (hKeq ▸ hk))
  obtain ⟨haM, la, hla, hal⟩ := decomp a ha
  obtain ⟨hbM, lb, hlb, hbl⟩ := decomp b hb'
  have hcomm := hβ U inf_le_left hU3 _ (inU a ha haM la hla hal) _ (inU b hb' hbM lb hlb hbl)
  refine (mem_blockCentralizer_iff (⟨a, haM⟩ * ⟨b, hbM⟩ * (⟨a, haM⟩)⁻¹ * (⟨b, hbM⟩)⁻¹)).mpr ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  set ga := mk ⟨a, haM⟩
  set gb := mk ⟨b, hbM⟩
  set ya := mk ⟨la, hLM hla⟩
  set yb := mk ⟨lb, hLM hlb⟩
  have hya : ya ∈ Lb := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hla)
  have hyb : yb ∈ Lb := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hlb)
  have y1 : yb⁻¹ * y * yb ∈ Lb := Lb.mul_mem (Lb.mul_mem (Lb.inv_mem hyb) hy) hyb
  have y2 : ya⁻¹ * (yb⁻¹ * y * yb) * ya ∈ Lb :=
    Lb.mul_mem (Lb.mul_mem (Lb.inv_mem hya) y1) hya
  have y3 : yb * (ya⁻¹ * (yb⁻¹ * y * yb) * ya) * yb⁻¹ ∈ Lb :=
    Lb.mul_mem (Lb.mul_mem hyb y2) (Lb.inv_mem hyb)
  have e1 := actInv gb yb hyb hbl y hy
  have e2 := actInv ga ya hya hal _ y1
  have e3 := act gb yb hyb hbl _ y2
  have e4 := act ga ya hya hal _ y3
  have hk := Subgroup.mem_centralizer_iff.mp hcomm y hy
  have key : ga * gb * ga⁻¹ * gb⁻¹ * y * (ga * gb * ga⁻¹ * gb⁻¹)⁻¹ = y := by
    calc ga * gb * ga⁻¹ * gb⁻¹ * y * (ga * gb * ga⁻¹ * gb⁻¹)⁻¹
        = ga * (gb * (ga⁻¹ * (gb⁻¹ * y * gb) * ga) * gb⁻¹) * ga⁻¹ := by group
      _ = ga * (gb * (ga⁻¹ * (yb⁻¹ * y * yb) * ga) * gb⁻¹) * ga⁻¹ := by rw [e1]
      _ = ga * (gb * (ya⁻¹ * (yb⁻¹ * y * yb) * ya) * gb⁻¹) * ga⁻¹ := by rw [e2]
      _ = ga * (yb * (ya⁻¹ * (yb⁻¹ * y * yb) * ya) * yb⁻¹) * ga⁻¹ := by rw [e3]
      _ = ya * (yb * (ya⁻¹ * (yb⁻¹ * y * yb) * ya) * yb⁻¹) * ya⁻¹ := by rw [e4]
      _ = ya * yb * ya⁻¹ * yb⁻¹ * y * (ya * yb * ya⁻¹ * yb⁻¹)⁻¹ := by group
      _ = y * (ya * yb * ya⁻¹ * yb⁻¹) * (ya * yb * ya⁻¹ * yb⁻¹)⁻¹ := by rw [← hk]
      _ = y := by group
  simp only [map_mul, map_inv]
  calc y * (ga * gb * ga⁻¹ * gb⁻¹)
      = (ga * gb * ga⁻¹ * gb⁻¹ * y * (ga * gb * ga⁻¹ * gb⁻¹)⁻¹) * (ga * gb * ga⁻¹ * gb⁻¹) := by
        rw [key]
    _ = ga * gb * ga⁻¹ * gb⁻¹ * y := by group

theorem D1J3Data.relIndex_inner_le (h : D1J3Data P M H R) (h85 : Asc81bEightFive)
    (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hBlk : KFactBlockThreeSolvable) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    (R ⊓ (L ⊔ blockCentralizer M L)).relIndex R ≤ 3 := by
  have h3 := h.surv.ph3
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  set S := pCoreOf 2 H with hSdef
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLbdef
  set Cb := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  set C := blockCentralizer M L with hCdef
  have hLM : L ≤ M := hL.le
  have hCM : C ≤ M := blockCentralizer_le M L
  have hRM : R ≤ M := h3.le_M
  have hR3 : IsPGroup 3 R := h3.isPGroup_R
  have hRL := h.le_normalizer_block hB3 hL
  obtain ⟨-, hγ⟩ := hBlk G M S L (GLBPrimeCore 3 H) (R ⊔ GLBPrimeCore 3 H) h3.isKGroup.1
    h3.asc81bHyp hL (h3.nineThree_not_one h85 hD2 hL).1 (h3.not_isSylowTwoOf_inf h85 hD2 hL)
    le_sup_right (hKeq ▸ sup_le h3.le_inf (le_inf (glbPrimeCore_le 3 H) h3.primeCore_le))
    (hKeq ▸ (inf_le_left.trans (le_normalizer_glbPrimeCore 3 H))) (hKeq ▸ h.normal_sup)
    (glbPrimeCore_coprime 3 H)
    (fun x hx => exists_pow_mem_of_mem_sup_of_le_normalizer h3.isPGroup_R
      (h3.le_H.trans (le_normalizer_glbPrimeCore 3 H)) hx)
    (fun k hk => h.two_top k (hKeq ▸ hk))
  have hUS : barM M R ≤ barM M (Subgroup.normalizer (S : Set G)) :=
    Subgroup.map_mono (Subgroup.comap_mono ((hKeq ▸ h3.le_inf).trans inf_le_right))
  have hUN : barM M R ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hL' : L.map (MulAut.conj (x : G)).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRL (Subgroup.mem_subgroupOf.mp hx))
    have hLbar : (barM M L).map (MulAut.conj (mk x)).toMonoidHom = barM M L := by
      rw [← barM_map_conj x.2, hL']
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hLbar
  have hU3 : IsPGroup 3 (barM M R) := (hR3.comap_subtype (K := M)).map _
  have hle := hγ (barM M R) hUS hUN hU3
  have hQ3 : (3 : ℕ).Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hcardbar : ∀ A : Subgroup G, A ≤ R → Nat.card (barM M A) = Nat.card A := by
    intro A hAR
    have hAp : IsPGroup 3 (A.subgroupOf M) := (hR3.to_le hAR).comap_subtype
    rw [barM, card_map_mk_of_isPGroup Nat.prime_three _ hQ3 hAp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAR.trans hRM)).toEquiv]
  have hCL : C ≤ Subgroup.normalizer (L : Set G) := by
    have hbarC : barM M C ≤ Cb := by
      rintro _ ⟨⟨c, hcM⟩, hc, rfl⟩
      exact (mem_blockCentralizer_iff ⟨c, hcM⟩).mp (Subgroup.mem_subgroupOf.mp hc)
    exact hL.toIsTwoPrimeComponent.le_normalizer
      (hbarC.trans (Subgroup.centralizer_le_normalizer _)) hCM
  have hLbCb : Lb ≤ Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.le_normalizer.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  have hbar : barM M (R ⊓ (L ⊔ C)) = barM M R ⊓ (Lb ⊔ Cb) := by
    apply le_antisymm
    · refine le_inf (Subgroup.map_mono (Subgroup.comap_mono inf_le_left)) ?_
      rintro _ ⟨x, hx, rfl⟩
      have hxLC : (x : G) ∈ ((C ⊔ L : Subgroup G) : Set G) := by
        rw [sup_comm]
        exact (Subgroup.mem_subgroupOf.mp hx).2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ L hCL] at hxLC
      obtain ⟨c, hc, l, hl, hcl⟩ := hxLC
      have hcM := hCM hc
      have e : x = ⟨c, hcM⟩ * ⟨l, hLM hl⟩ := Subtype.ext hcl.symm
      rw [e, map_mul]
      exact (Lb ⊔ Cb).mul_mem
        (Subgroup.mem_sup_right ((mem_blockCentralizer_iff ⟨c, hcM⟩).mp hc))
        (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl)))
    · rintro z ⟨⟨r, hr, rfl⟩, hz⟩
      have hz' : mk r ∈ ((Lb ⊔ Cb : Subgroup _) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := hz
      rw [Subgroup.coe_mul_of_left_le_normalizer_right Lb Cb hLbCb] at hz'
      obtain ⟨_, ⟨l, hl, rfl⟩, c, hc, hlc⟩ := hz'
      have hc' : mk (l⁻¹ * r) ∈ Cb := by
        rw [map_mul, map_inv, ← hlc, inv_mul_cancel_left]
        exact hc
      have hlr : ((l⁻¹ * r : M) : G) ∈ C := (mem_blockCentralizer_iff _).mpr hc'
      have hrLC : (r : G) ∈ L ⊔ C := by
        have e : (r : G) = (l : G) * ((l⁻¹ * r : M) : G) := by simp
        rw [e]
        exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hl) hlr
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
        ⟨Subgroup.mem_subgroupOf.mp hr, hrLC⟩)
  have h1 := Subgroup.relIndex_mul_card (R ⊓ (L ⊔ C)) R
  have h2 := Subgroup.relIndex_mul_card (barM M R ⊓ (Lb ⊔ Cb)) (barM M R)
  rw [inf_right_comm, inf_idem] at h1 h2
  rw [← hbar, hcardbar _ inf_le_left, hcardbar R le_rfl] at h2
  rw [hbar] at h2
  have hpos : 0 < Nat.card (R ⊓ (L ⊔ C) : Subgroup G) := Nat.card_pos
  have heq : (R ⊓ (L ⊔ C)).relIndex R = (barM M R ⊓ (Lb ⊔ Cb)).relIndex (barM M R) :=
    Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  rw [heq]
  exact hle

end J3MSide

section J3MSideAssembly

variable {G : Type} [Group G] [Finite G]

theorem stmtJ3MSide_of (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (hD2 : D1NoXBlock) (hB3 : StmtBlockThree) (hBlk : KFactBlockThreeSolvable)
    (hb : StmtBlockInnerNormalizer) : StmtJ3MSide := by
  intro G _ _ P M H R h hO
  obtain ⟨s, hsK, hsR, hs2, hsing⟩ := h.singer
  obtain ⟨a, haR, b, hbR, hab⟩ := h.nonabelian
  have hR3 : IsPGroup 3 R := h.surv.ph3.isPGroup_R
  by_cases hall : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      R ≤ L ⊔ blockCentralizer M L
  · apply hab
    have h1 := h.faithful h84 hD2 hB3 hO (R.mul_mem (R.mul_mem (R.mul_mem haR hbR)
      (R.inv_mem haR)) (R.inv_mem hbR)) fun L hL =>
        h.commutator_mem_blockCentralizer h84 h85 h86 hD2 hBlk hb hL ⟨haR, hall L hL haR⟩
          ⟨hbR, hall L hL hbR⟩
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  · push Not at hall
    obtain ⟨L, hL, hRL⟩ := hall
    have hle := h.relIndex_inner_le h85 hD2 hB3 hBlk hL
    have hdvd : (R ⊓ (L ⊔ blockCentralizer M L)).relIndex R ∣ Nat.card R :=
      Subgroup.relIndex_dvd_card _ _
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR3
    rw [hk] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hne : (R ⊓ (L ⊔ blockCentralizer M L)).relIndex R ≠ 1 := by
      intro h1
      apply hRL
      have := Subgroup.relIndex_eq_one.mp h1
      exact this.trans inf_le_right
    have h3 : (R ⊓ (L ⊔ blockCentralizer M L)).relIndex R = 3 := by
      rw [hj] at hle hne ⊢
      rcases j with _ | _ | j
      · simp at hne
      · simp
      · exfalso
        have h9 : 3 ^ 2 ≤ 3 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h9' : (9 : ℕ) ≤ 3 ^ (j + 1 + 1) := by simpa using h9
        omega
    have hs2M : s ^ 2 ∈ M := M.pow_mem hsK.2 2
    have hs2R : s ^ 2 ∈ Subgroup.normalizer (R : Set G) :=
      Subgroup.pow_mem _ hsR 2
    exact hsing _ inf_le_left h3 (D1J3Data.mem_normalizer_inner hs2M hs2R
      (h.sq_mem_normalizer hB3 hsK hs2 hL))

end J3MSideAssembly

end CFSG.AGLEmbedding
