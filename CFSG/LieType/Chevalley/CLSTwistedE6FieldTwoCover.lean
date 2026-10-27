module

public import CFSG.LieType.Chevalley.CLSTwistedE6FieldTwoCoverLifts

public noncomputable section

namespace CFSG.LieType.Chevalley.TwistedE6FieldTwoCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.RelativeRoots CFSG.LieType.Chevalley.C2E6Std.TwistedE6LeviCover
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover
open Subgroup
open scoped commutatorElement

theorem height_nsmul_add_nsmul (a b : ℕ) (α β : Fin Tag.F4.rank → ℤ) :
    height (a • α + b • β) = a * height α + b * height β := by
  unfold height
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [nsmul_eq_mul]

theorem height_lt_of_mem_relSupport {α β γ : Fin Tag.F4.rank → ℤ} (hαp : 0 < height α)
    (hβp : 0 < height β) (hγ : γ ∈ relSupport α β) :
    height α < height γ ∧ height β < height γ ∧ IsRoot .F4 γ ∧ 0 < height γ := by
  obtain ⟨hγr, a, b, ha, hb, rfl⟩ := hγ
  rw [height_nsmul_add_nsmul]
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  refine ⟨by nlinarith, by nlinarith, hγr, by nlinarith⟩

theorem twisted_E6_field_two_central_two_kernel_elementary
    {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (η : E →* stdGroup) (hη : Function.Surjective η)
    (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) :
    (∀ c ∈ η.ker, c ^ 2 = 1) ∧ CFSG.IsElementaryAbelian 2 η.ker := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  choose! y hy hy2 using fun r (g : stdGroup) (hg : g ∈ relG r) =>
    exists_lift_mul_self_relG hη hC h2 hg
  set D := kerSq η hC with hD
  have : D.Normal := Subgroup.normal_of_le_center (kerSq_le_center hC)
  have hDle : D ≤ η.ker := fun c hc => hc.1
  set η' : E ⧸ D →* stdGroup := QuotientGroup.lift D η hDle with hη'
  have hη'mk : ∀ e : E, η' (e : E ⧸ D) = η e := fun e => QuotientGroup.lift_mk _ _ _
  have hmk : ∀ {a b : E}, a * b⁻¹ ∈ D → (a : E ⧸ D) = b := fun h =>
    QuotientGroup.eq_iff_div_mem.mpr (by rwa [div_eq_mul_inv])
  have hone : ∀ r, ((y r 1 : E) : E ⧸ D) = 1 := fun r =>
    (QuotientGroup.eq_one_iff _).2 ⟨by rw [hy r 1 (one_mem _)], hy2 r 1 (one_mem _)⟩
  have hmul : ∀ r (g g' : stdGroup), g ∈ relG r → g' ∈ relG r →
      ((y r (g * g') : E) : E ⧸ D) = (y r g : E ⧸ D) * (y r g' : E ⧸ D) := by
    intro r g g' hg hg'
    have hgg' := mul_mem hg hg'
    have hab := liftsCommute_relG_self hη hC h2 hg hg' _ _ (hy r g hg) (hy r g' hg')
    have hac := liftsCommute_relG_self hη hC h2 hg hgg' _ _ (hy r g hg) (hy r _ hgg')
    have hbc := liftsCommute_relG_self hη hC h2 hg' hgg' _ _ (hy r g' hg') (hy r _ hgg')
    rw [← QuotientGroup.mk_mul]
    refine (hmk ?_).symm
    refine ⟨by rw [map_mul, map_inv, map_mul, hy r g hg, hy r g' hg', hy r _ hgg',
      mul_inv_cancel], ?_⟩
    set a := y r g
    set b := y r g'
    set c := y r (g * g')
    have hc' : c⁻¹ = c := inv_eq_of_mul_eq_one_right (hy2 r _ hgg')
    rw [hc']
    calc a * b * c * (a * b * c) = (a * a) * (b * b) * (c * c) := by
          calc a * b * c * (a * b * c) = a * b * (c * a) * b * c := by group
            _ = a * b * (a * c) * b * c := by rw [hac]
            _ = a * (b * a) * c * b * c := by group
            _ = a * (a * b) * c * b * c := by rw [hab]
            _ = a * a * b * (c * b) * c := by group
            _ = a * a * b * (b * c) * c := by rw [hbc]
            _ = (a * a) * (b * b) * (c * c) := by group
      _ = 1 := by rw [hy2 r g hg, hy2 r g' hg', hy2 r _ hgg', one_mul, one_mul]
  set ψ : (r : Fin Tag.F4.rank → ℤ) → relG r →* E ⧸ D := fun r =>
    { toFun := fun g => (y r g : E ⧸ D)
      map_one' := hone r
      map_mul' := fun g g' => hmul r g g' g.2 g'.2 } with hψ
  have hψapply : ∀ r (g : relG r), ψ r g = (y r g : E ⧸ D) := fun _ _ => rfl
  set Y : (Fin Tag.F4.rank → ℤ) → Subgroup (E ⧸ D) := fun r => (ψ r).range with hYdef
  have hYmem : ∀ r (g : stdGroup) (hg : g ∈ relG r), (y r g : E ⧸ D) ∈ Y r :=
    fun r g hg => ⟨⟨g, hg⟩, rfl⟩
  have hrel : ∀ α β, IsRoot .F4 α → 0 < height α → IsRoot .F4 β → 0 < height β → α ≠ β →
      ∀ a ∈ Y α, ∀ b ∈ Y β, ⁅a, b⁆ ∈ ⨆ γ ∈ relSupport α β, Y γ := by
    rintro α β hα hαp hβ hβp hne _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
    have hne' : α ≠ -β := fun e => by
      have : height α = -height β := by rw [e]; simp [height]
      omega
    obtain ⟨z, hz, hzk⟩ := exists_commutator_lift_mem hη hC h2 y hy hy2 hα hβ hne hne' g.2 h.2
    have e : ⁅(y α g : E ⧸ D), (y β h : E ⧸ D)⁆ = ((⁅y α g, y β h⁆ : E) : E ⧸ D) :=
      (map_commutatorElement (QuotientGroup.mk' D) _ _).symm
    rw [hψapply, hψapply, e, hmk hzk]
    have hle : Subgroup.closure {x | ∃ γ ∈ relSupport α β, ∃ k ∈ relG γ, y γ k = x} ≤
        (⨆ γ ∈ relSupport α β, Y γ).comap (QuotientGroup.mk' D) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨γ, hγ, k, hk, rfl⟩
      exact (le_iSup₂ (f := fun γ (_ : γ ∈ relSupport α β) => Y γ) γ hγ) (hYmem γ k hk)
    exact hle hz
  have hfin : {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α ∧ 0 < height α}.Finite :=
    (finite_setOf_isRoot .F4).subset fun _ h => h.1
  set T := hfin.toFinset with hTdef
  have hT : ∀ α ∈ T, IsRoot .F4 α ∧ 0 < height α := fun α hα => (Set.Finite.mem_toFinset hfin).1 hα
  have hcl : ∀ α ∈ T, ∀ β ∈ T, α ≠ β → ∀ γ ∈ relSupport α β, γ ∈ T := by
    intro α hα β hβ _ γ hγ
    obtain ⟨-, -, hγr, hγp⟩ := height_lt_of_mem_relSupport (hT α hα).2 (hT β hβ).2 hγ
    exact (Set.Finite.mem_toFinset hfin).2 ⟨hγr, hγp⟩
  have hcount := card_iSup_le_prod Y relSupport
    (fun α β _ hαp _ hβp _ γ hγ => (height_lt_of_mem_relSupport hαp hβp hγ).1) hrel T hT hcl
  have hYcard : ∀ α, Nat.card (Y α) ≤ Nat.card (relRootGroup α) := fun α => by
    rw [← card_relG α]
    exact Nat.card_le_card_of_surjective _ (ψ α).rangeRestrict_surjective
  set e : Fin T.card → Fin Tag.F4.rank → ℤ := fun j => (T.equivFin.symm j : Fin Tag.F4.rank → ℤ)
    with he
  have heinj : Function.Injective e := fun i j hij =>
    T.equivFin.symm.injective (Subtype.ext hij)
  have herange : Set.range e = {r | IsRoot Tag.F4 r ∧ 0 < height r} := by
    ext r
    constructor
    · rintro ⟨j, rfl⟩
      exact (Set.Finite.mem_toFinset hfin).1 (T.equivFin.symm j).2
    · intro hr
      refine ⟨T.equivFin ⟨r, (Set.Finite.mem_toFinset hfin).2 hr⟩, ?_⟩
      simp [he]
  have hbij := bijOn_prod_relRootGroup e heinj herange
  have hcardU : Nat.card (graphFixedPosUnipotent TwistTag.E6 K barHom) =
      ∏ α ∈ T, Nat.card (relRootGroup α) := by
    have h1 : Nat.card (graphFixedPosUnipotent TwistTag.E6 K barHom) =
        Nat.card ((j : Fin T.card) → relRootGroup (e j)) := by
      rw [← Nat.card_univ (α := (j : Fin T.card) → relRootGroup (e j))]
      exact (Nat.card_congr hbij.equiv).symm
    rw [h1, Nat.card_pi, ← Finset.prod_coe_sort T]
    exact Fintype.prod_equiv T.equivFin.symm _ _ fun j => rfl
  set P₀ := ⨆ α ∈ T, Y α with hP₀
  have hP₀card : Nat.card P₀ ≤ Nat.card (graphFixedPosUnipotent TwistTag.E6 K barHom) := by
    rw [hcardU]
    exact hcount.trans (Finset.prod_le_prod fun α _ => hYcard α)
  have hUle : (graphFixedPosUnipotent TwistTag.E6 K barHom).subgroupOf stdGroup ≤ P₀.map η' := by
    intro x hx
    obtain ⟨u, -, hux⟩ := hbij.surjOn hx
    set l : List stdGroup := List.ofFn fun j =>
      (⟨(u j : ModGL TwistTag.E6.tag K), relRootGroup_le_stdGroup _ (u j).2⟩ : stdGroup) with hl
    have hxl : x = l.prod := by
      apply Subtype.ext
      refine hux.symm.trans ?_
      have e1 : ((l.prod : stdGroup) : ModGL Tag.E6 K) = (l.map stdGroup.subtype).prod :=
        map_list_prod stdGroup.subtype l
      rw [e1, hl, List.map_ofFn]
      rfl
    rw [hxl]
    refine list_prod_mem fun a ha => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ha
    refine ⟨ψ (e j) ⟨⟨_, relRootGroup_le_stdGroup _ (u j).2⟩, (u j).2⟩, ?_, ?_⟩
    · exact (le_iSup₂ (f := fun α (_ : α ∈ T) => Y α) (e j) (T.equivFin.symm j).2)
        ⟨⟨⟨_, relRootGroup_le_stdGroup _ (u j).2⟩, (u j).2⟩, rfl⟩
    · rw [hψapply, hη'mk, hy _ _ (u j).2]
  have := finite_modGL (τ := Tag.E6) (K := K)
  set S : Sylow 2 stdGroup :=
    (isPGroup_graphFixedPosUnipotent_subgroupOf 2 (t := TwistTag.E6) (K := K)
      (σ := barHom)).toSylow
      (not_dvd_index_graphFixedPosUnipotent 2 (t := TwistTag.E6) barHom_surjective) with hS
  have hSle : (S : Subgroup stdGroup) ≤ P₀.map η' := by
    rw [hS, IsPGroup.toSylow_coe]
    exact hUle
  have hcardS : Nat.card (S : Subgroup stdGroup) =
      Nat.card (graphFixedPosUnipotent TwistTag.E6 K barHom) := by
    rw [hS, IsPGroup.toSylow_coe]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K barHom)).toEquiv
  have : Finite (P₀.map η') := Finite.of_surjective _ (η'.subgroupMap_surjective P₀)
  have hbij' : Function.Bijective (η'.subgroupMap P₀) := by
    refine (η'.subgroupMap_surjective P₀).bijective_of_nat_card_le ?_
    calc Nat.card P₀ ≤ Nat.card (graphFixedPosUnipotent TwistTag.E6 K barHom) := hP₀card
      _ = Nat.card (S : Subgroup stdGroup) := hcardS.symm
      _ ≤ Nat.card (P₀.map η') := Subgroup.card_le_of_le hSle
  have hinj : ∀ z ∈ P₀, η' z = 1 → z = 1 := by
    intro z hz hz1
    have h : η'.subgroupMap P₀ ⟨z, hz⟩ = η'.subgroupMap P₀ 1 :=
      Subtype.ext (by rw [map_one]; exact hz1)
    exact congrArg Subtype.val (hbij'.1 h)
  have hη'surj : Function.Surjective η' := by
    intro x
    obtain ⟨e, rfl⟩ := hη x
    exact ⟨e, hη'mk e⟩
  have hC' : η'.ker ≤ center (E ⧸ D) := by
    intro c hc
    induction c using QuotientGroup.induction_on with
    | H z =>
      rw [MonoidHom.mem_ker, hη'mk] at hc
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      induction g using QuotientGroup.induction_on with
      | H g =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp (hC hc) g]
  have h2' : IsPGroup 2 η'.ker := by
    rintro ⟨c, hc⟩
    induction c using QuotientGroup.induction_on with
    | H z =>
      rw [MonoidHom.mem_ker, hη'mk] at hc
      obtain ⟨n, hn⟩ := h2 ⟨z, hc⟩
      refine ⟨n, Subtype.ext ?_⟩
      have hz : z ^ 2 ^ n = 1 := by simpa using congrArg (fun w : η.ker => (w : E)) hn
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← QuotientGroup.mk_pow, hz, QuotientGroup.mk_one]
  have hbot := LinearCover.ker_eq_bot_of_sylow_le_map η' hη'surj hC' h2' S P₀ hSle hinj
  have hsq : ∀ c ∈ η.ker, c * c = 1 := by
    intro c hc
    have hc' : (c : E ⧸ D) ∈ η'.ker := by
      rw [MonoidHom.mem_ker, hη'mk]
      exact hc
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hc'
    exact hc'.2
  refine ⟨fun c hc => by rw [sq]; exact hsq c hc, ?_⟩
  exact { is_comm := ⟨fun u v => Subtype.ext (Subgroup.mem_center_iff.mp (hC v.2) u)⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
            Subtype.ext (by rw [SubgroupClass.coe_pow, sq, OneMemClass.coe_one]; exact hsq x x.2) }

end CFSG.LieType.Chevalley.TwistedE6FieldTwoCover
