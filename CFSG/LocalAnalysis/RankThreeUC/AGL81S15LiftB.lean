module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftLeaves
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsGroup

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open scoped commutatorElement

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding

theorem exists_perfect_centralizing_aux1 {G : Type} [Group G] {a b c d : G}
    (hab : Commute a b) (had : Commute a d) (hcb : Commute c b) (hcd : Commute c d) :
    ⁅a * b, c * d⁆ = ⁅a, c⁆ * ⁅b, d⁆ := by
  have h1 : Commute a⁻¹ (b * d * b⁻¹) :=
    (hab.inv_left.mul_right had.inv_left).mul_right hab.inv_left.inv_right
  have h2 : Commute c⁻¹ (b * d * b⁻¹ * d⁻¹) :=
    ((hcb.inv_left.mul_right hcd.inv_left).mul_right hcb.inv_left.inv_right).mul_right
      hcd.inv_left.inv_right
  have h3 : b * c = c * b := hcb.symm.eq
  calc ⁅a * b, c * d⁆ = a * (b * c) * (d * b⁻¹ * a⁻¹ * d⁻¹ * c⁻¹) := by
        simp only [commutatorElement_def, mul_inv_rev]; group
    _ = a * (c * b) * (d * b⁻¹ * a⁻¹ * d⁻¹ * c⁻¹) := by rw [h3]
    _ = a * c * ((b * d * b⁻¹) * a⁻¹) * (d⁻¹ * c⁻¹) := by group
    _ = a * c * (a⁻¹ * (b * d * b⁻¹)) * (d⁻¹ * c⁻¹) := by rw [← h1.eq]
    _ = a * c * a⁻¹ * ((b * d * b⁻¹ * d⁻¹) * c⁻¹) := by group
    _ = a * c * a⁻¹ * (c⁻¹ * (b * d * b⁻¹ * d⁻¹)) := by rw [← h2.eq]
    _ = ⁅a, c⁆ * ⁅b, d⁆ := by simp only [commutatorElement_def]; group

theorem perfect_le_sup_centralizer_component {Y : Type} [Group Y] [Finite Y]
    (hSch : KSch) (hY : CFSG.Open.IsKGroup Y) (E J : Subgroup Y) (hE : ⁅E, E⁆ = E)
    (hJ : CFSG.Open.IsComponentOf J ⊤) (hEJ : E ≤ Subgroup.normalizer (J : Set Y)) :
    E ≤ J ⊔ Subgroup.centralizer (J : Set Y) := by
  have hSS : CFSG.ComponentClassification.LBalance.SchreierSections Y := hSch.schreierSections hY
  haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2
  have hnab : ∃ a b : ↥J ⧸ Subgroup.center ↥J, a * b ≠ b * a := by
    by_contra hcon
    exact quotient_center_nonabelian_of_isQuasisimple hJ.2.2
      ⟨⟨fun a b => by by_contra h; exact hcon ⟨a, b, h⟩⟩⟩
  haveI hOutQ : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (↥J ⧸ Subgroup.center ↥J)) :=
    hSS.outer_solvable J hnab (QuotientGroup.mk' (Subgroup.center ↥J))
      (QuotientGroup.mk'_surjective _)
  haveI : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
  haveI : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥J) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient ↥J
  haveI : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.2 hE
  let action : ↥E →* MulAut ↥J := J.normalizerMonoidHom.comp (Subgroup.inclusion hEJ)
  intro e he
  obtain ⟨j, hj⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner action
    ⟨e, he⟩
  have hconj : ∀ y ∈ J, e * y * e⁻¹ = (j : Y) * y * (j : Y)⁻¹ := by
    intro y hy
    have h1 := congrArg (fun a : MulAut ↥J => ((a ⟨y, hy⟩ : ↥J) : Y)) hj
    exact h1
  have hcent : (j : Y)⁻¹ * e ∈ Subgroup.centralizer (J : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h2 := hconj y hy
    calc y * ((j : Y)⁻¹ * e) = (j : Y)⁻¹ * ((j : Y) * y * (j : Y)⁻¹) * e := by group
      _ = (j : Y)⁻¹ * (e * y * e⁻¹) * e := by rw [h2]
      _ = (j : Y)⁻¹ * e * y := by group
  have hmem : e = (j : Y) * ((j : Y)⁻¹ * e) := by group
  rw [hmem]
  exact Subgroup.mul_mem_sup j.2 hcent

theorem perfect_le_layer_sup_centralizer_aux1 {Y : Type} [Group Y] {A B C : Subgroup Y}
    (h1 : CFSG.Open.IsSubnormal A B) (h2 : CFSG.Open.IsSubnormal B C) :
    CFSG.Open.IsSubnormal A C := by
  induction h1 with
  | refl H => exact h2
  | @step H M K hHM hnorm hMK ih => exact CFSG.Open.IsSubnormal.step hHM hnorm (ih h2)

theorem perfect_le_layer_sup_centralizer_aux2 {Y : Type} [Group Y] (Chat : Subgroup Y) [Chat.Normal]
    {J : Subgroup Y} (hJ : CFSG.Open.IsComponentOf J Chat) : CFSG.Open.IsComponentOf J ⊤ :=
  ⟨le_top, perfect_le_layer_sup_centralizer_aux1 hJ.2.1
    (CFSG.Open.IsSubnormal.step le_top inferInstance (CFSG.Open.IsSubnormal.refl ⊤)), hJ.2.2⟩

theorem perfect_le_layer_sup_centralizer_aux3 {Y : Type} [Group Y] (J : Subgroup Y) {e : Y}
    (he : e ∈ J ⊔ Subgroup.centralizer (J : Set Y)) :
    ∃ j ∈ J, ∀ y ∈ J, e * y * e⁻¹ = j * y * j⁻¹ := by
  have h1 : e ∈ ((J ⊔ Subgroup.centralizer (J : Set Y) : Subgroup Y) : Set Y) := he
  rw [Subgroup.coe_mul_of_right_le_normalizer_left J _
    (Subgroup.centralizer_le_normalizer _)] at h1
  obtain ⟨j, hj, c, hc, rfl⟩ := h1
  refine ⟨j, hj, fun y hy => ?_⟩
  have h2 : y * c = c * y := Subgroup.mem_centralizer_iff.1 hc y hy
  have h3 : c * y * c⁻¹ = y := by rw [← h2]; group
  calc j * c * y * (j * c)⁻¹ = j * (c * y * c⁻¹) * j⁻¹ := by group
    _ = j * y * j⁻¹ := by rw [h3]

theorem perfect_le_layer_sup_centralizer_aux4 {Y : Type} [Group Y] [Finite Y]
    (hSch : KSch) (hY : CFSG.Open.IsKGroup Y) (E : Subgroup Y) (hE : ⁅E, E⁆ = E)
    (S : Finset (Subgroup Y)) (hS : ∀ J ∈ S, CFSG.Open.IsComponentOf J ⊤)
    (hn : ∀ J ∈ S, E ≤ Subgroup.normalizer (J : Set Y)) (e : Y) (he : e ∈ E) :
    ∃ x ∈ S.sup id, ∀ J ∈ S, ∀ y ∈ J, e * y * e⁻¹ = x * y * x⁻¹ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | insert J₀ S hJ₀ ih =>
    obtain ⟨x, hx, hxS⟩ := ih (fun J hJ => hS J (Finset.mem_insert_of_mem hJ))
      (fun J hJ => hn J (Finset.mem_insert_of_mem hJ))
    have hJ₀c : CFSG.Open.IsComponentOf J₀ ⊤ := hS J₀ (Finset.mem_insert_self _ _)
    obtain ⟨j, hjJ, hj⟩ := perfect_le_layer_sup_centralizer_aux3 J₀
      (perfect_le_sup_centralizer_component hSch hY E J₀ hE hJ₀c
        (hn J₀ (Finset.mem_insert_self _ _)) he)
    have hcomm : ∀ J ∈ S, ⁅J, J₀⁆ = ⊥ := fun J hJ =>
      kComp_holds.1 Y J J₀ (hS J (Finset.mem_insert_of_mem hJ)) hJ₀c
        (fun h => hJ₀ (h ▸ hJ))
    have hxJ₀ : x ∈ Subgroup.centralizer (J₀ : Set Y) := by
      have : S.sup id ≤ Subgroup.centralizer (J₀ : Set Y) :=
        Finset.sup_le fun J hJ => Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm J hJ)
      exact this hx
    refine ⟨x * j, ?_, ?_⟩
    · rw [Finset.sup_insert]
      exact (J₀ ⊔ S.sup id).mul_mem (Subgroup.mem_sup_right hx) (Subgroup.mem_sup_left hjJ)
    · intro J hJ y hy
      rcases Finset.mem_insert.1 hJ with rfl | hJS
      · have h1 : (j * y * j⁻¹) * x = x * (j * y * j⁻¹) :=
          Subgroup.mem_centralizer_iff.1 hxJ₀ _
            (J.mul_mem (J.mul_mem hjJ hy) (J.inv_mem hjJ))
        calc e * y * e⁻¹ = j * y * j⁻¹ := hj y hy
          _ = x * (j * y * j⁻¹) * x⁻¹ := by rw [← h1]; group
          _ = x * j * y * (x * j)⁻¹ := by group
      · have hjJc : j ∈ Subgroup.centralizer (J : Set Y) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.1
            (by rw [Subgroup.commutator_comm]; exact hcomm J hJS) hjJ
        have h1 : y * j = j * y := Subgroup.mem_centralizer_iff.1 hjJc y hy
        calc e * y * e⁻¹ = x * y * x⁻¹ := hxS J hJS y hy
          _ = x * (j * y * j⁻¹) * x⁻¹ := by rw [← h1]; group
          _ = x * j * y * (x * j)⁻¹ := by group

theorem perfect_le_layer_sup_centralizer {Y : Type} [Group Y] [Finite Y]
    (hSch : KSch) (hY : CFSG.Open.IsKGroup Y) (Chat : Subgroup Y) [Chat.Normal]
    (E : Subgroup Y) (hE : ⁅E, E⁆ = E)
    (hn : ∀ J : Subgroup Y, CFSG.Open.IsComponentOf J Chat → E ≤ Subgroup.normalizer (J : Set Y)) :
    E ≤ layerIn Chat ⊔ Subgroup.centralizer (layerIn Chat : Set Y) := by
  classical
  have hfin : Set.Finite {J : Subgroup Y | CFSG.Open.IsComponentOf J Chat} := Set.toFinite _
  set S : Finset (Subgroup Y) := hfin.toFinset with hSdef
  have hmem : ∀ J, J ∈ S ↔ CFSG.Open.IsComponentOf J Chat := fun J => by
    simp [hSdef]
  have hlayer : layerIn Chat = S.sup id := by
    unfold layerIn
    rw [Finset.sup_id_eq_sSup, hSdef, Set.Finite.coe_toFinset]
  intro e he
  obtain ⟨x, hx, hxS⟩ := perfect_le_layer_sup_centralizer_aux4 hSch hY E hE S
    (fun J hJ => perfect_le_layer_sup_centralizer_aux2 Chat ((hmem J).1 hJ))
    (fun J hJ => hn J ((hmem J).1 hJ)) e he
  rw [hlayer]
  have hc : x⁻¹ * e ∈ Subgroup.centralizer ((S.sup id : Subgroup Y) : Set Y) := by
    have hle : S.sup id ≤ Subgroup.centralizer ({x⁻¹ * e} : Set Y) := by
      refine Finset.sup_le fun J hJ y hy => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      rw [Set.mem_singleton_iff] at hc
      subst hc
      have h2 := hxS J hJ y hy
      calc x⁻¹ * e * y = x⁻¹ * (e * y * e⁻¹) * e := by group
        _ = x⁻¹ * (x * y * x⁻¹) * e := by rw [h2]
        _ = y * (x⁻¹ * e) := by group
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.1 (hle hz) (x⁻¹ * e) (Set.mem_singleton _)).symm
  have hmem' : e = x * (x⁻¹ * e) := by group
  rw [hmem']
  exact Subgroup.mul_mem_sup hx hc

theorem exists_perfect_centralizing {Y : Type} [Group Y] [Finite Y] (L E : Subgroup Y)
    (hE : ⁅E, E⁆ = E) (hEn : E ≤ Subgroup.normalizer (L : Set Y))
    (hEL : E ≤ L ⊔ Subgroup.centralizer (L : Set Y)) :
    ∃ E₂ : Subgroup Y, ⁅E₂, E₂⁆ = E₂ ∧ E₂ ≤ E ⊔ L ∧ E₂ ≤ Subgroup.centralizer (L : Set Y) ∧
      E ≤ E₂ ⊔ L ∧ (E₂.subgroupOf (E ⊔ L)).Normal := by
  set C : Subgroup Y := Subgroup.centralizer (L : Set Y) with hC
  set G₁ : Subgroup Y := E ⊔ L with hG₁
  set B₀ : Subgroup Y := G₁ ⊓ C with hB₀
  set E₂ : Subgroup Y := ⁅B₀, B₀⁆ with hE₂
  have hCN : C ≤ Subgroup.normalizer (L : Set Y) := Subgroup.centralizer_le_normalizer _
  have hG₁N : G₁ ≤ Subgroup.normalizer (L : Set Y) := sup_le hEn Subgroup.le_normalizer
  have hCL : ∀ c ∈ C, ∀ l ∈ L, Commute l c := fun c hc l hl =>
    Subgroup.mem_centralizer_iff.1 hc l hl
  have hE₂B : E₂ ≤ B₀ := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hE₂G : E₂ ≤ G₁ := hE₂B.trans inf_le_left
  have hE₂C : E₂ ≤ C := hE₂B.trans inf_le_right
  have hdec : ∀ e ∈ E, ∃ l ∈ L, ∃ c ∈ B₀, e = l * c := by
    intro e he
    have h1 : e ∈ ((L ⊔ C : Subgroup Y) : Set Y) := hEL he
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L C hCN] at h1
    obtain ⟨l, hl, c, hc, rfl⟩ := h1
    refine ⟨l, hl, c, ⟨?_, hc⟩, rfl⟩
    have : c = l⁻¹ * (l * c) := by group
    rw [this]
    exact G₁.mul_mem (G₁.inv_mem (Subgroup.mem_sup_right hl)) (Subgroup.mem_sup_left he)
  have hdE : E ≤ E₂ ⊔ L := by
    have h : ⁅E, E⁆ ≤ E₂ ⊔ L := by
      rw [Subgroup.commutator_le]
      intro e₁ he₁ e₂ he₂
      obtain ⟨l₁, hl₁, c₁, hc₁, rfl⟩ := hdec e₁ he₁
      obtain ⟨l₂, hl₂, c₂, hc₂, rfl⟩ := hdec e₂ he₂
      rw [exists_perfect_centralizing_aux1 (hCL c₁ hc₁.2 l₁ hl₁) (hCL c₂ hc₂.2 l₁ hl₁)
        (hCL c₁ hc₁.2 l₂ hl₂) (hCL c₂ hc₂.2 l₂ hl₂)]
      have hlL : ⁅l₁, l₂⁆ ∈ L :=
        Subgroup.commutator_le_of_le le_rfl le_rfl (Subgroup.commutator_mem_commutator hl₁ hl₂)
      exact (E₂ ⊔ L).mul_mem (Subgroup.mem_sup_right hlL)
        (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hc₁ hc₂))
    rwa [hE] at h
  have hB₀dec : ∀ b ∈ B₀, ∃ u ∈ E₂, ∃ z ∈ L, z ∈ B₀ ∧ b = u * z := by
    intro b hb
    have h1 : b ∈ ((E ⊔ L : Subgroup Y) : Set Y) := hb.1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right E L hEn] at h1
    obtain ⟨e, he, l₀, hl₀, rfl⟩ := h1
    have h2 : e ∈ ((E₂ ⊔ L : Subgroup Y) : Set Y) := hdE he
    rw [Subgroup.coe_mul_of_left_le_normalizer_right E₂ L (hE₂C.trans hCN)] at h2
    obtain ⟨u, hu, l₁, hl₁, rfl⟩ := h2
    refine ⟨u, hu, l₁ * l₀, L.mul_mem hl₁ hl₀, ?_, by group⟩
    have : l₁ * l₀ = u⁻¹ * (u * l₁ * l₀) := by group
    rw [this]
    exact B₀.mul_mem (B₀.inv_mem (hE₂B hu)) hb
  have hperf : ⁅E₂, E₂⁆ = E₂ := by
    apply le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl)
    show ⁅B₀, B₀⁆ ≤ ⁅E₂, E₂⁆
    rw [Subgroup.commutator_le]
    intro b₁ hb₁ b₂ hb₂
    obtain ⟨u₁, hu₁, z₁, hz₁, hz₁B, rfl⟩ := hB₀dec b₁ hb₁
    obtain ⟨u₂, hu₂, z₂, hz₂, hz₂B, rfl⟩ := hB₀dec b₂ hb₂
    rw [exists_perfect_centralizing_aux1 (hCL u₁ (hE₂C hu₁) z₁ hz₁).symm
      (hCL u₁ (hE₂C hu₁) z₂ hz₂).symm (hCL u₂ (hE₂C hu₂) z₁ hz₁).symm
      (hCL u₂ (hE₂C hu₂) z₂ hz₂).symm]
    have hzz : ⁅z₁, z₂⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (hCL z₂ hz₂B.2 z₁ hz₁).eq
    rw [hzz, mul_one]
    exact Subgroup.commutator_mem_commutator hu₁ hu₂
  have hnorm : (E₂.subgroupOf G₁).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hE₂G]
    intro h k hh hk
    have hmapB : B₀.map (MulAut.conj k).toMonoidHom ≤ B₀ := by
      rintro _ ⟨b, hb, rfl⟩
      refine ⟨G₁.mul_mem (G₁.mul_mem hk hb.1) (G₁.inv_mem hk), ?_⟩
      show k * b * k⁻¹ ∈ C
      rw [hC, Subgroup.mem_centralizer_iff]
      intro l hl
      have hkl : k⁻¹ * l * k ∈ L := (Subgroup.mem_normalizer_iff''.1 (hG₁N hk) l).1 hl
      have h3 := (hCL b hb.2 _ hkl).eq
      show l * (k * b * k⁻¹) = k * b * k⁻¹ * l
      calc l * (k * b * k⁻¹) = k * ((k⁻¹ * l * k) * b) * k⁻¹ := by group
        _ = k * (b * (k⁻¹ * l * k)) * k⁻¹ := by rw [h3]
        _ = k * b * k⁻¹ * l := by group
    have hmapE : E₂.map (MulAut.conj k).toMonoidHom ≤ E₂ := by
      rw [hE₂, Subgroup.map_commutator]
      exact Subgroup.commutator_mono hmapB hmapB
    exact hmapE ⟨h, hh, rfl⟩
  exact ⟨E₂, hperf, hE₂G, hE₂C, hdE, hnorm⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
