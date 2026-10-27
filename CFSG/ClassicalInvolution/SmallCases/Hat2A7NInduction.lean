module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7NDefs

public section

namespace CFSG.ClassicalInvolution.Hat2A7N

open CFSG.Open CFSG.ClassicalInvolution.Hat2A7
open scoped commutatorElement

section Instance

variable {F : Type} [Group F]

theorem commOrEq_of_oddCore_central [Finite F] (hB : CITBelow2A7 (Nat.card F)) {x : F}
    (hx : Subgroup.centralizer ({x} : Set F) ≠ ⊤) {L M : Subgroup F} {u v : F}
    (hL : IsClassical2A7 (Subgroup.centralizer ({x} : Set F)) L u)
    (hM : IsClassical2A7 (Subgroup.centralizer ({x} : Set F)) M v)
    (hOc : classicalInvolutionOddCore
        ↥(normalClosureIn2A7 (Subgroup.centralizer ({x} : Set F)) (L ⊔ M)) ≤
      Subgroup.center ↥(normalClosureIn2A7 (Subgroup.centralizer ({x} : Set F)) (L ⊔ M))) :
    CommOrEq L M := by
  set C : Subgroup F := Subgroup.centralizer ({x} : Set F) with hC
  set Y₀ : Subgroup F := normalClosureIn2A7 C (L ⊔ M) with hY₀
  have hLM : L ⊔ M ≤ C := sup_le hL.le hM.le
  have hY₀C : Y₀ ≤ C := normalClosureIn2A7_le hLM
  have hLY₀ : L ≤ Y₀ := le_sup_left.trans le_normalClosureIn2A7
  have hMY₀ : M ≤ Y₀ := le_sup_right.trans le_normalClosureIn2A7
  have hY₀ne : Y₀ ≠ ⊤ := fun h => hx (top_le_iff.mp (h ▸ hY₀C))
  have hlt : Nat.card Y₀ < Nat.card F := card_lt_of_ne_top' hY₀ne
  have hLc : ∀ c ∈ C, L.map (MulAut.conj c).toMonoidHom ≤ Y₀ := fun c hc =>
    (Subgroup.map_mono le_sup_left).trans (map_conj_le_normalClosureIn2A7 hc)
  have hMc : ∀ c ∈ C, M.map (MulAut.conj c).toMonoidHom ≤ Y₀ := fun c hc =>
    (Subgroup.map_mono le_sup_right).trans (map_conj_le_normalClosureIn2A7 hc)
  let Λ₀ : Set (Subgroup ↥Y₀) :=
    {N' | ∃ c ∈ C, N' = (L.map (MulAut.conj c).toMonoidHom).subgroupOf Y₀ ∨
      N' = (M.map (MulAut.conj c).toMonoidHom).subgroupOf Y₀}
  have hL1 : L.map (MulAut.conj (1 : F)).toMonoidHom = L := map_conj_one L
  have hM1 : M.map (MulAut.conj (1 : F)).toMonoidHom = M := map_conj_one M
  have hLΛ : L.subgroupOf Y₀ ∈ Λ₀ := ⟨1, C.one_mem, Or.inl (by rw [hL1])⟩
  have hMΛ : M.subgroupOf Y₀ ∈ Λ₀ := ⟨1, C.one_mem, Or.inr (by rw [hM1])⟩
  have hΛ₀ : InClass2A7 Λ₀ := by
    refine ⟨⟨_, hLΛ⟩, ?_, ?_, ?_⟩
    · rintro g _ ⟨c, hc, hN | hN⟩
      · refine ⟨(g : F) * c, C.mul_mem (hY₀C g.2) hc, Or.inl ?_⟩
        rw [hN, map_conj_subgroupOf, map_map_conj]
      · refine ⟨(g : F) * c, C.mul_mem (hY₀C g.2) hc, Or.inr ?_⟩
        rw [hN, map_conj_subgroupOf, map_map_conj]
    · have hmapG : (⨆ N' ∈ Λ₀, N').map Y₀.subtype = Y₀ := by
        apply le_antisymm (Subgroup.map_subtype_le _)
        apply normalClosureIn2A7_le_of
        intro c hc
        rw [Subgroup.map_sup]
        have key : ∀ {H : Subgroup F}, H ≤ Y₀ → H.subgroupOf Y₀ ∈ Λ₀ →
            H ≤ (⨆ N' ∈ Λ₀, N').map Y₀.subtype := by
          intro H hH hmem
          have hle : H.subgroupOf Y₀ ≤ ⨆ N' ∈ Λ₀, N' := le_iSup₂_of_le _ hmem le_rfl
          calc H = (H.subgroupOf Y₀).map Y₀.subtype := by
                rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hH]
            _ ≤ _ := Subgroup.map_mono hle
        exact sup_le (key (hLc c hc) ⟨c, hc, Or.inl rfl⟩) (key (hMc c hc) ⟨c, hc, Or.inr rfl⟩)
      apply Subgroup.map_injective Y₀.subtype_injective
      rw [hmapG, Subgroup.map_top, Subgroup.range_subtype]
    · rintro N' ⟨c, hc, hN | hN⟩
      · subst hN
        have h1 := hL.conj c
        rw [map_conj_eq_of_mem hc] at h1
        exact ⟨_, h1.subgroupOf (hLc c hc) hY₀C⟩
      · subst hN
        have h1 := hM.conj c
        rw [map_conj_eq_of_mem hc] at h1
        exact ⟨_, h1.subgroupOf (hMc c hc) hY₀C⟩
  obtain ⟨D⟩ := hB ↥Y₀ hlt Λ₀ hΛ₀
  have hLcl := hL.subgroupOf hLY₀ hY₀C
  have hMcl := hM.subgroupOf hMY₀ hY₀C
  have hperfL : ⁅L.subgroupOf Y₀, L.subgroupOf Y₀⁆ = L.subgroupOf Y₀ :=
    Subgroup.isPerfect_iff.mp hLcl.perfect
  have hperfM : ⁅M.subgroupOf Y₀, M.subgroupOf Y₀⁆ = M.subgroupOf Y₀ :=
    Subgroup.isPerfect_iff.mp hMcl.perfect
  have hmemL : (L.subgroupOf Y₀).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y₀)) ∈
      oddQuotientFamily2A7 Λ₀ := ⟨_, hLΛ, rfl⟩
  have hmemM : (M.subgroupOf Y₀).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y₀)) ∈
      oddQuotientFamily2A7 Λ₀ := ⟨_, hMΛ, rfl⟩
  rw [D.members] at hmemL hmemM
  obtain ⟨i, hi⟩ := hmemL
  obtain ⟨j, hj⟩ := hmemM
  by_cases hij : i = j
  · subst hij
    left
    have heq : (L.subgroupOf Y₀).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y₀)) =
        (M.subgroupOf Y₀).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y₀)) :=
      hi.symm.trans hj
    have h2 := Subgroup.subgroupOf_inj.mp
      (eq_of_map_mk_eq_of_le_center hOc hperfL hperfM heq)
    have e1 : L ⊓ Y₀ = L := inf_eq_left.mpr hLY₀
    have e2 : M ⊓ Y₀ = M := inf_eq_left.mpr hMY₀
    rw [e1, e2] at h2
    exact h2
  · right
    intro a ha b hb
    have hcomm := commutes_of_map_commutes_of_le_center hOc hperfL (M := M.subgroupOf Y₀)
      (fun a' ha' b' hb' => by
        have := D.commute i j hij _ (hi ▸ Subgroup.mem_map_of_mem _ ha') _
          (hj ▸ Subgroup.mem_map_of_mem _ hb')
        exact this)
    exact congrArg Subtype.val (hcomm ⟨a, hLY₀ ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
      ⟨b, hMY₀ hb⟩ (Subgroup.mem_subgroupOf.mpr hb))

theorem oddCore_le_center_of_central [Finite F] {L : Subgroup F} {u : F}
    (hL : IsClassical2A7 ⊤ L u)
    (h1 : classicalInvolutionOddCore
        ↥(normalClosureIn2A7 (Subgroup.centralizer ({u} : Set F)) (L ⊔ L)) ≤
      Subgroup.center ↥(normalClosureIn2A7 (Subgroup.centralizer ({u} : Set F)) (L ⊔ L))) :
    classicalInvolutionOddCore ↥L ≤ Subgroup.center ↥L := by
  set C : Subgroup F := Subgroup.centralizer ({u} : Set F) with hC
  have hLC : IsClassical2A7 C L u := hL.mono hL.le_centralizer le_top
  set Y₀ : Subgroup F := normalClosureIn2A7 C (L ⊔ L) with hY₀
  have hLY₀ : L ≤ Y₀ := le_sup_left.trans le_normalClosureIn2A7
  have hY₀C : Y₀ ≤ C := normalClosureIn2A7_le (sup_le hLC.le hLC.le)
  have hsub : IsSubnormal L Y₀ := by
    have h2 := isSubnormal_inf hLC.subnormal Y₀
    have e1 : L ⊓ Y₀ = L := inf_eq_left.mpr hLY₀
    have e2 : (C ⊓ Subgroup.centralizer ({u} : Set F)) ⊓ Y₀ = Y₀ := by
      rw [← hC, inf_idem]
      exact inf_eq_right.mpr hY₀C
    rwa [e1, e2] at h2
  intro e he
  rw [Subgroup.mem_center_iff]
  intro l
  obtain ⟨hY, hmemY⟩ :=
    (CFSG.ComponentClassification.OddCore.subnormal_mem_iff hsub e.1 e.2).mp he
  have hc := h1 hmemY
  have hcomm := Subgroup.mem_center_iff.mp hc ⟨l.1, hLY₀ l.2⟩
  have h3 : (l : F) * (e : F) = (e : F) * (l : F) := congrArg Subtype.val hcomm
  exact Subtype.ext h3

end Instance

section NarrowedTight

variable {F : Type} [Group F]

theorem centralizer_ne_top_of_orderOf_eq_two
    (hZ : ∀ x : F, (∀ y : F, x * y = y * x) → x = 1) {x : F} (hx : orderOf x = 2) :
    Subgroup.centralizer ({x} : Set F) ≠ ⊤ := by
  intro h
  have hx1 : x = 1 := hZ x fun y => by
    have hy : y ∈ Subgroup.centralizer ({x} : Set F) := h ▸ Subgroup.mem_top y
    exact Subgroup.mem_centralizer_iff.mp hy x rfl
  rw [hx1, orderOf_one] at hx
  omega

theorem tightIH_of_localOddCentral [Finite F] (hB : CITBelow2A7 (Nat.card F))
    (hZ : ∀ x : F, (∀ y : F, x * y = y * x) → x = 1) {K : Subgroup F} {z : F}
    (hO : LocalOddCentral2A7N F K z) : TightIH K z := by
  intro x hx2 hxE L M u v hadm hM hL hMc
  have hne := centralizer_ne_top_of_orderOf_eq_two hZ hx2
  exact commOrEq_of_oddCore_central hB hne hL hMc (hO x hx2 hxE hne L M u v hadm hM hL hMc)

theorem tightP1_of_localOddCentral [Finite F]
    (hZ : ∀ x : F, (∀ y : F, x * y = y * x) → x = 1) {K : Subgroup F} {z : F}
    (hK : IsClassical2A7 ⊤ K z) (hO : LocalOddCentral2A7N F K z) : TightP1 K := by
  intro L u hLc hL
  obtain ⟨g, rfl⟩ := hLc
  have hKg : IsClassical2A7 ⊤ (K.map (MulAut.conj g).toMonoidHom) (g * z * g⁻¹) := by
    have h1 := hK.conj g
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h1
  have hu : u = g * z * g⁻¹ := hKg.eq_of_orderOf_eq_two hL.mem hL.orderOf_eq_two
  have hu2 := hL.orderOf_eq_two
  have hne := centralizer_ne_top_of_orderOf_eq_two hZ hu2
  have hLC : IsClassical2A7 (Subgroup.centralizer ({u} : Set F))
      (K.map (MulAut.conj g).toMonoidHom) u := hL.mono hL.le_centralizer le_top
  exact oddCore_le_center_of_central hL
    (hO u hu2 (isCommProd_of_mem_classOf ⟨g, hu.symm⟩) hne _ _ u u
      (Or.inl ⟨g, rfl⟩) ⟨g, rfl⟩ hLC hLC)

theorem tightSettingN_of_localOddCentral [Finite F] (hB : CITBelow2A7 (Nat.card F))
    (hZ : ∀ x : F, (∀ y : F, x * y = y * x) → x = 1) {K : Subgroup F} {z : F}
    (hK : IsClassical2A7 ⊤ K z)
    (ht : Subgroup.centralizer ({z} : Set F) ≤ Subgroup.normalizer (K : Set F))
    (hO : LocalOddCentral2A7N F K z) : TightSettingN F K z :=
  ⟨⟨hK, ht⟩, hZ, tightIH_of_localOddCentral hB hZ hO, tightP1_of_localOddCentral hZ hK hO⟩

end NarrowedTight

end CFSG.ClassicalInvolution.Hat2A7N
