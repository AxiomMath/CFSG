module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15OraclesCyc
public import CFSG.HardMathSupport.Solomon.Proving.LBLemma27
public import CFSG.GH74.GLS.Stage2.Signalizer.Bridge
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.RankThree.PartTwo.Sec4.T444.Coprime

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open scoped commutatorElement

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding

@[expose] def layerIn {Y : Type} [Group Y] (H : Subgroup Y) : Subgroup Y :=
  sSup {J : Subgroup Y | CFSG.Open.IsComponentOf J H}

@[expose] def fstarIn {Y : Type} [Group Y] (H : Subgroup Y) : Subgroup Y :=
  (CFSG.generalizedFitting ↥H).map H.subtype

open scoped MatrixGroups in
@[expose] def K63List (r : ℕ) (S : Type) [Group S] : Prop :=
  Nonempty (S ≃* PSL(2, ZMod r)) ∨ Nonempty (S ≃* PSL(3, ZMod r)) ∨
    ((r = 3 ∨ r = 5) ∧ Nonempty (S ≃* alternatingGroup (Fin 5))) ∨
    (r = 5 ∧ Nonempty (S ≃* alternatingGroup (Fin 6))) ∨
    (r = 7 ∧ Nonempty (S ≃* alternatingGroup (Fin 7)))

@[expose] def LiftsExist {X : Type} [Group X] [Finite X] (T T₁ T₂ : Subgroup X) : Prop :=
  ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls → ∃ L : Subgroup X, LiftOf T L Ls

@[expose] def barToStar {X : Type} [Group X] (T : Subgroup X) (hle : CFSG.pCore 2 X ≤ gnC T) :
    X ⧸ CFSG.pCore 2 X →* X ⧸ gnC T :=
  QuotientGroup.map (CFSG.pCore 2 X) (gnC T) (MonoidHom.id X) (by simpa using hle)

@[expose] def zPre {Y Z : Type} [Group Y] [Group Z] (π : Y →* Z) (Ls : Subgroup Z) (V : Subgroup Y) :
    Subgroup Y :=
  V ⊓ ((Subgroup.center ↥Ls).map Ls.subtype).comap π

theorem exists_minimal_supplement {Y : Type} [Group Y] [Finite Y] (Chat E₂ : Subgroup Y) [Chat.Normal]
    (hperf : ⁅E₂ ⊔ Chat, E₂ ⊔ Chat⁆ ⊔ Chat = E₂ ⊔ Chat) :
    ∃ V : Subgroup Y, V ≤ E₂ ∧ V ⊔ Chat = E₂ ⊔ Chat ∧ ⁅V, V⁆ = V ∧
      Group.IsNilpotent ↥(V ⊓ Chat) ∧ ∀ W : Subgroup Y, W ≤ V → W ⊔ Chat = E₂ ⊔ Chat → W = V := by
  classical
  have hne : {V : Subgroup Y | V ≤ E₂ ∧ V ⊔ Chat = E₂ ⊔ Chat}.Nonempty := ⟨E₂, le_rfl, rfl⟩
  obtain ⟨V, ⟨hVE, hVsup⟩, hmin⟩ := (wellFounded_lt (α := Subgroup Y)).has_min _ hne
  have hmin' : ∀ W : Subgroup Y, W ≤ V → W ⊔ Chat = E₂ ⊔ Chat → W = V := by
    intro W hWV hW
    by_contra hne'
    exact hmin W ⟨hWV.trans hVE, hW⟩ (lt_of_le_of_ne hWV hne')
  have hfrat : (V ⊓ Chat).subgroupOf V ≤ frattini ↥V := by
    unfold frattini Order.radical
    simp only [le_iInf_iff]
    intro K hK
    by_contra hXK
    have hsup : K ⊔ (V ⊓ Chat).subgroupOf V = ⊤ := by
      refine hK.2 _ (left_lt_sup.2 hXK)
    have hWV : K.map V.subtype ≤ V := Subgroup.map_subtype_le K
    have hXmap : ((V ⊓ Chat).subgroupOf V).map V.subtype = V ⊓ Chat :=
      Subgroup.map_subgroupOf_eq_of_le inf_le_left
    have hVeq : V = K.map V.subtype ⊔ (V ⊓ Chat) := by
      have h1 : (K ⊔ (V ⊓ Chat).subgroupOf V).map V.subtype = V := by
        rw [hsup, Subgroup.map_top, Subgroup.range_subtype]
      rw [Subgroup.map_sup, hXmap] at h1
      exact h1.symm
    have hW : K.map V.subtype ⊔ Chat = E₂ ⊔ Chat := by
      apply le_antisymm
      · exact sup_le_sup_right (hWV.trans hVE) _
      · rw [← hVsup]
        refine sup_le ?_ le_sup_right
        calc V = K.map V.subtype ⊔ (V ⊓ Chat) := hVeq
          _ ≤ K.map V.subtype ⊔ Chat := sup_le_sup_left inf_le_right _
    have hWeq := hmin' _ hWV hW
    apply hK.1
    apply Subgroup.map_injective V.subtype_injective
    rw [hWeq, Subgroup.map_top, Subgroup.range_subtype]
  have hnil : Group.IsNilpotent ↥(V ⊓ Chat) := by
    haveI : Group.IsNilpotent ↥(frattini ↥V) := frattini_nilpotent
    haveI h1 : Group.IsNilpotent ↥(((V ⊓ Chat).subgroupOf V).subgroupOf (frattini ↥V)) :=
      inferInstance
    haveI h2 : Group.IsNilpotent ↥((V ⊓ Chat).subgroupOf V) :=
      nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hfrat)
    exact nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (inf_le_left : V ⊓ Chat ≤ V))
  have hVC : V ≤ ⁅V, V⁆ ⊔ Chat := by
    set π := QuotientGroup.mk' Chat with hπ
    have hmapC : Chat.map π = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨c, hc, rfl⟩
      simpa [hπ, QuotientGroup.eq_one_iff] using hc
    have hA : (E₂ ⊔ Chat).map π = V.map π := by
      rw [← hVsup, Subgroup.map_sup, hmapC, sup_bot_eq]
    have h1 : ⁅V.map π, V.map π⁆ = V.map π := by
      calc ⁅V.map π, V.map π⁆ = ⁅(E₂ ⊔ Chat).map π, (E₂ ⊔ Chat).map π⁆ := by rw [hA]
        _ = (⁅E₂ ⊔ Chat, E₂ ⊔ Chat⁆).map π := (Subgroup.map_commutator _ _ _).symm
        _ = (⁅E₂ ⊔ Chat, E₂ ⊔ Chat⁆ ⊔ Chat).map π := by
          rw [Subgroup.map_sup, hmapC, sup_bot_eq]
        _ = (E₂ ⊔ Chat).map π := by rw [hperf]
        _ = V.map π := hA
    have h2 : (⁅V, V⁆).map π = V.map π := by rw [Subgroup.map_commutator, h1]
    intro v hv
    have h3 : π v ∈ (⁅V, V⁆).map π := by
      rw [h2]
      exact Subgroup.mem_map_of_mem _ hv
    have h4 : v ∈ ((⁅V, V⁆).map π).comap π := h3
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h4
  have hVeq : V = ⁅V, V⁆ ⊔ (V ⊓ Chat) := by
    apply le_antisymm
    · intro v hv
      obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (hVC hv)
      have haV : a ∈ V := Subgroup.commutator_le_of_le (le_refl V) (le_refl V) ha
      have hcV : c ∈ V := by
        have : a⁻¹ * (a * c) ∈ V := V.mul_mem (V.inv_mem haV) hv
        simpa using this
      exact Subgroup.mul_mem_sup ha ⟨hcV, hc⟩
    · exact sup_le (Subgroup.commutator_le_of_le (le_refl V) (le_refl V)) inf_le_left
  have hperfV : ⁅V, V⁆ = V := by
    have hmapC : ((⁅V, V⁆).subgroupOf V).map V.subtype = ⁅V, V⁆ :=
      Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le (le_refl V) (le_refl V))
    have hXmap : ((V ⊓ Chat).subgroupOf V).map V.subtype = V ⊓ Chat :=
      Subgroup.map_subgroupOf_eq_of_le inf_le_left
    have hC : (⁅V, V⁆).subgroupOf V ⊔ frattini ↥V = ⊤ := by
      apply Subgroup.map_injective V.subtype_injective
      rw [Subgroup.map_top, Subgroup.range_subtype]
      apply le_antisymm
      · exact Subgroup.map_subtype_le _
      · calc V = ⁅V, V⁆ ⊔ (V ⊓ Chat) := hVeq
          _ = ((⁅V, V⁆).subgroupOf V).map V.subtype ⊔ ((V ⊓ Chat).subgroupOf V).map V.subtype := by
            rw [hmapC, hXmap]
          _ ≤ ((⁅V, V⁆).subgroupOf V ⊔ frattini ↥V).map V.subtype := by
            rw [← Subgroup.map_sup]
            exact Subgroup.map_mono (sup_le_sup_left hfrat _)
    have hC' := frattini_nongenerating hC
    calc ⁅V, V⁆ = ((⁅V, V⁆).subgroupOf V).map V.subtype := hmapC.symm
      _ = V := by rw [hC', Subgroup.map_top, Subgroup.range_subtype]
  exact ⟨V, hVE, hVsup, hperfV, hnil, hmin'⟩

theorem quasisimple_normal_le_center_or_eq {W : Type} [Group W] (hq : CFSG.Open.IsQuasisimple W)
    (N : Subgroup W) [N.Normal] : N ≤ Subgroup.center W ∨ N = ⊤ := by
  haveI := hq.2
  have hmapN : (N.map (QuotientGroup.mk' (Subgroup.center W))).Normal :=
    Subgroup.Normal.map ‹N.Normal› _ (QuotientGroup.mk'_surjective _)
  rcases hmapN.eq_bot_or_eq_top with h | h
  · left
    intro n hn
    have : QuotientGroup.mk' (Subgroup.center W) n ∈ N.map (QuotientGroup.mk' (Subgroup.center W)) :=
      Subgroup.mem_map_of_mem _ hn
    rw [h] at this
    simpa [QuotientGroup.eq_one_iff] using this
  · right
    have key : ∀ (n m z : W), z ∈ Subgroup.center W → ⁅n * z, m⁆ = ⁅n, m⁆ := by
      intro n m z hz
      have hc : Commute z m := ((Subgroup.mem_center_iff.1 hz) m).symm
      have h1 : z * m * z⁻¹ = m := hc.mul_inv_cancel
      calc ⁅n * z, m⁆ = n * (z * m * z⁻¹) * n⁻¹ * m⁻¹ := by
            simp [commutatorElement_def, mul_assoc]
        _ = ⁅n, m⁆ := by rw [h1]; simp [commutatorElement_def]
    have hdec : ∀ w : W, ∃ n ∈ N, ∃ z ∈ Subgroup.center W, w = n * z := by
      intro w
      have : QuotientGroup.mk' (Subgroup.center W) w ∈ N.map (QuotientGroup.mk' (Subgroup.center W)) := by
        rw [h]; trivial
      obtain ⟨n, hn, hnw⟩ := this
      refine ⟨n, hn, n⁻¹ * w, ?_, by simp⟩
      have : (n⁻¹ * w : W) ∈ (QuotientGroup.mk' (Subgroup.center W)).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hnw]; simp
      simpa using this
    have hcomm : ⁅(⊤ : Subgroup W), ⊤⁆ ≤ N := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hdec a
      obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hdec b
      rw [key _ _ _ hz₁, ← commutatorElement_inv, key _ _ _ hz₂, commutatorElement_inv]
      exact Subgroup.commutator_le_right N N (Subgroup.commutator_mem_commutator hn₁ hn₂)
    have : (⊤ : Subgroup W) ≤ N := by
      have := hq.1
      rw [commutator_def] at this
      rw [← this]
      exact hcomm
    exact top_le_iff.1 this

theorem centralizer_conj_mem {Y : Type} [Group Y] (Q : Subgroup Y) [Q.Normal] {g n : Y}
    (hn : n ∈ Subgroup.centralizer (Q : Set Y)) :
    g * n * g⁻¹ ∈ Subgroup.centralizer (Q : Set Y) := by
  rw [Subgroup.mem_centralizer_iff] at hn ⊢
  intro h hh
  have h1 : g⁻¹ * h * g ∈ Q := by
    simpa using ‹Q.Normal›.conj_mem h hh g⁻¹
  have h2 := hn _ h1
  calc h * (g * n * g⁻¹) = g * ((g⁻¹ * h * g) * n) * g⁻¹ := by group
    _ = g * (n * (g⁻¹ * h * g)) * g⁻¹ := by rw [h2]
    _ = g * n * g⁻¹ * h := by group

theorem centralizes_or_solvable {Y Z : Type} [Group Y] [Finite Y] [Group Z] (π : Y →* Z)
    (Ls : Subgroup Z) (hLs : CFSG.Open.IsComponentOf Ls ⊤) (V : Subgroup Y) (hVs : V.map π = Ls)
    (hmin : ∀ W : Subgroup Y, W ≤ V → W.map π = Ls → W = V)
    (hnil : Group.IsNilpotent ↥(V ⊓ π.ker)) (Q : Subgroup Y) [Q.Normal] :
    V ≤ Subgroup.centralizer (Q : Set Y) ∨
      (Group.IsSolvable ↥(V ⊓ Subgroup.centralizer (Q : Set Y)) ∧
        (V ⊓ Subgroup.centralizer (Q : Set Y)).map π ≤ (Subgroup.center ↥Ls).map Ls.subtype) := by
  set D : Subgroup Y := V ⊓ Subgroup.centralizer (Q : Set Y) with hD
  have hDV : D ≤ V := inf_le_left
  have hle : D.map π ≤ Ls := by
    rw [← hVs]
    exact Subgroup.map_mono hDV
  have hnorm : ∀ l ∈ Ls, ∀ x ∈ D.map π, l * x * l⁻¹ ∈ D.map π := by
    intro l hl x hx
    rw [← hVs] at hl
    obtain ⟨v, hv, rfl⟩ := hl
    obtain ⟨d, hd, rfl⟩ := hx
    refine ⟨v * d * v⁻¹, ⟨V.mul_mem (V.mul_mem hv hd.1) (V.inv_mem hv),
      centralizer_conj_mem Q hd.2⟩, by simp⟩
  haveI hN : ((D.map π).subgroupOf Ls).Normal :=
    ⟨fun n hn g => by
      have := hnorm g.1 g.2 n.1 hn
      exact this⟩
  rcases quasisimple_normal_le_center_or_eq hLs.2.2 ((D.map π).subgroupOf Ls) with h | h
  · right
    have hcent : D.map π ≤ (Subgroup.center ↥Ls).map Ls.subtype := by
      intro x hx
      have hxL : x ∈ Ls := hle hx
      exact ⟨⟨x, hxL⟩, h (show (⟨x, hxL⟩ : ↥Ls) ∈ (D.map π).subgroupOf Ls from hx), rfl⟩
    refine ⟨?_, hcent⟩
    haveI hKnil : Group.IsNilpotent ↥(D ⊓ π.ker) := by
      haveI : Group.IsNilpotent ↥((D ⊓ π.ker).subgroupOf (V ⊓ π.ker)) := inferInstance
      exact nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (inf_le_inf_right _ hDV : D ⊓ π.ker ≤ V ⊓ π.ker))
    haveI : Group.IsSolvable ↥(D ⊓ π.ker) := inferInstance
    haveI : Group.IsSolvable ↥(D.map π) := by
      apply Group.isSolvable_of_comm
      intro a b
      obtain ⟨z, hz, hza⟩ := hcent a.2
      apply Subtype.ext
      have h1 := congrArg Subtype.val
        ((Subgroup.mem_center_iff.1 hz) (⟨b.1, hle b.2⟩ : ↥Ls))
      change (a : Z) * b = b * a
      rw [← hza]
      exact h1.symm
    let g : ↥D →* ↥(D.map π) :=
      (π.comp D.subtype).codRestrict (D.map π) (fun d => ⟨d.1, d.2, rfl⟩)
    let f : ↥(D ⊓ π.ker) →* ↥D := Subgroup.inclusion inf_le_left
    refine solvable_of_ker_le_range f g ?_
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : π x.1 = 1 := congrArg Subtype.val hx
    exact ⟨⟨x.1, x.2, h1⟩, rfl⟩
  · left
    have hDmap : D.map π = Ls := by
      apply le_antisymm hle
      intro l hl
      have : (⟨l, hl⟩ : ↥Ls) ∈ (D.map π).subgroupOf Ls := by rw [h]; trivial
      exact this
    have hDeq := hmin D hDV hDmap
    rw [← hDeq]
    exact inf_le_right

theorem perfect_le_centralizer_of_cyclic {Y : Type} [Group Y] (Q V : Subgroup Y) [Q.Normal]
    (hQ : IsCyclic ↥Q) (hV : ⁅V, V⁆ = V) : V ≤ Subgroup.centralizer (Q : Set Y) := by
  let ρ : ↥V →* MulAut ↥Q := (MulAut.conjNormal (H := Q)).comp V.subtype
  have hcomm : ∀ a b : MulAut ↥Q, a * b = b * a := by
    intro a b
    apply (IsCyclic.mulAutMulEquiv ↥Q).injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hK : ⁅V, V⁆ ≤ ρ.ker.map V.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : ↥V), ⟨b, hb⟩⁆, ?_, rfl⟩
    refine (MonoidHom.mem_ker).2 ?_
    rw [map_commutatorElement]
    exact (commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _))
  intro v hv
  rw [hV] at hK
  obtain ⟨k, hk, hkv⟩ := hK hv
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have h1 := congrArg (fun a : MulAut ↥Q => (a ⟨q, hq⟩ : Y)) (MonoidHom.mem_ker.1 hk)
  simp only [MulAut.one_apply] at h1
  have h2 : (ρ k : MulAut ↥Q) ⟨q, hq⟩ = ⟨v * q * v⁻¹, by
      simpa using ‹Q.Normal›.conj_mem q hq v⟩ := by
    apply Subtype.ext
    have hkv' : (k : Y) = v := hkv
    change (k : Y) * q * (k : Y)⁻¹ = v * q * v⁻¹
    rw [hkv']
  rw [h2] at h1
  change v * q * v⁻¹ = q at h1
  calc q * v = v * q * v⁻¹ * v := by rw [h1]
    _ = v * q := by group

theorem barToStar_surjective {X : Type} [Group X] (T : Subgroup X)
    (hle : CFSG.pCore 2 X ≤ gnC T) : Function.Surjective (barToStar T hle) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨QuotientGroup.mk x, rfl⟩

theorem ker_barToStar {X : Type} [Group X] (T : Subgroup X) (hle : CFSG.pCore 2 X ≤ gnC T) :
    (barToStar T hle).ker = (gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [MonoidHom.mem_ker]
  change (QuotientGroup.mk x : X ⧸ gnC T) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨c, hc, hcx⟩
    have h1 : c⁻¹ * x ∈ CFSG.pCore 2 X := QuotientGroup.eq.1 hcx
    have hx : x = c * (c⁻¹ * x) := by group
    rw [hx]
    exact (gnC T).mul_mem hc (hle h1)

theorem commutator_eq_self_of_isQuasisimple {Z : Type} [Group Z] {Ls : Subgroup Z}
    (h : CFSG.Open.IsQuasisimple ↥Ls) : ⁅Ls, Ls⁆ = Ls := by
  apply le_antisymm (Subgroup.commutator_le_of_le (le_refl Ls) (le_refl Ls))
  intro x hx
  have h1 : ⁅(⊤ : Subgroup ↥Ls), (⊤ : Subgroup ↥Ls)⁆ = ⊤ := by
    have := h.1
    rwa [commutator_def] at this
  have h2 : (⟨x, hx⟩ : ↥Ls) ∈ ⁅(⊤ : Subgroup ↥Ls), (⊤ : Subgroup ↥Ls)⁆ := by
    rw [h1]
    exact Subgroup.mem_top _
  have h3 := Subgroup.mem_map_of_mem Ls.subtype h2
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h3
  exact h3

theorem quotient_center_nonabelian_of_isQuasisimple {W : Type} [Group W]
    (h : CFSG.Open.IsQuasisimple W) : ¬ IsMulCommutative (W ⧸ Subgroup.center W) := by
  intro hc
  haveI := h.2
  have hZ : Subgroup.center W = ⊤ := by
    apply top_le_iff.1
    have h1 : ⁅(⊤ : Subgroup W), (⊤ : Subgroup W)⁆ = ⊤ := by
      have := h.1
      rwa [commutator_def] at this
    rw [← h1, Subgroup.commutator_le]
    intro a _ b _
    have h2 : (QuotientGroup.mk' (Subgroup.center W)) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hc.is_comm.comm _ _)
    exact (QuotientGroup.eq_one_iff _).1 h2
  obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial (W ⧸ Subgroup.center W)).exists_pair_ne
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  have ha : (QuotientGroup.mk a : W ⧸ Subgroup.center W) = 1 :=
    (QuotientGroup.eq_one_iff a).2 (hZ ▸ Subgroup.mem_top a)
  have hb : (QuotientGroup.mk b : W ⧸ Subgroup.center W) = 1 :=
    (QuotientGroup.eq_one_iff b).2 (hZ ▸ Subgroup.mem_top b)
  exact hxy (ha.trans hb.symm)

theorem zPre_normal {Y Z : Type} [Group Y] [Group Z] (π : Y →* Z) (Ls : Subgroup Z)
    (V : Subgroup Y) (hV : V.map π ≤ Ls) : ((zPre π Ls V).subgroupOf V).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨z, hz, hzn⟩ := hn.2
  have hgL : π g.1 ∈ Ls := hV ⟨g.1, g.2, rfl⟩
  refine ⟨V.mul_mem (V.mul_mem g.2 n.2) (V.inv_mem g.2), ?_⟩
  change π (g.1 * n.1 * g.1⁻¹) ∈ (Subgroup.center ↥Ls).map Ls.subtype
  rw [map_mul, map_mul, map_inv]
  refine ⟨z, hz, ?_⟩
  have h1 := congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨π g.1, hgL⟩)
  change π g.1 * (z : Z) = (z : Z) * π g.1 at h1
  have h2 : (z : Z) = π n.1 := hzn
  rw [← h2]
  change (z : Z) = π g.1 * (z : Z) * (π g.1)⁻¹
  rw [h1]
  group

theorem zPre_equiv {Y Z : Type} [Group Y] [Group Z] (π : Y →* Z) (Ls : Subgroup Z)
    (V : Subgroup Y) (hV : V.map π = Ls) [((zPre π Ls V).subgroupOf V).Normal] :
    Nonempty (↥V ⧸ (zPre π Ls V).subgroupOf V ≃* ↥Ls ⧸ Subgroup.center ↥Ls) := by
  have hmem : ∀ v : ↥V, π v.1 ∈ Ls := fun v => by
    rw [← hV]
    exact Subgroup.mem_map_of_mem π v.2
  let φ : ↥V →* ↥Ls := (π.comp V.subtype).codRestrict Ls hmem
  let ψ : ↥V →* ↥Ls ⧸ Subgroup.center ↥Ls := (QuotientGroup.mk' (Subgroup.center ↥Ls)).comp φ
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have hl : (l : Z) ∈ V.map π := by rw [hV]; exact l.2
    obtain ⟨v, hv, hvl⟩ := hl
    have hφ : φ ⟨v, hv⟩ = l := Subtype.ext hvl
    exact ⟨⟨v, hv⟩, by
      change (QuotientGroup.mk' (Subgroup.center ↥Ls)) (φ ⟨v, hv⟩) = _
      rw [hφ]
      rfl⟩
  have hker : ψ.ker = (zPre π Ls V).subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk' (Subgroup.center ↥Ls)) (φ v) = 1 ↔ _
    rw [show (QuotientGroup.mk' (Subgroup.center ↥Ls)) (φ v) = (φ v : ↥Ls ⧸ Subgroup.center ↥Ls)
      from rfl, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨v.2, ⟨φ v, h, rfl⟩⟩
    · rintro ⟨-, z, hz, hzv⟩
      have : z = φ v := Subtype.ext hzv
      rwa [← this]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

@[expose] def ShapeI1 (S : Type) [Group S] : Prop :=
  (IsClassicalTwoOrG2 S ∧ ¬ RankOneChevTwo S) ∨
    ∃ n : ℕ, (n = 7 ∨ (8 < n ∧ Even n)) ∧ Nonempty (S ≃* alternatingGroup (Fin n))

theorem isClassicalTwoOrG2_of_equiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : IsClassicalTwoOrG2 S) : IsClassicalTwoOrG2 S' := by
  rcases h with ⟨d, hd, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.symm.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩)
  · exact Or.inr (Or.inr ⟨d, hd, ⟨e.symm.trans f⟩⟩)

theorem rankOneChevTwo_of_equiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : RankOneChevTwo S) : RankOneChevTwo S' := by
  rcases h with ⟨d, hd, ⟨f⟩⟩ | h
  · exact Or.inl ⟨d, hd, ⟨e.symm.trans f⟩⟩
  · obtain ⟨f⟩ := h
    exact Or.inr ⟨e.symm.trans f⟩

theorem ShapeI1.of_equiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S') (h : ShapeI1 S) :
    ShapeI1 S' := by
  rcases h with ⟨h1, h2⟩ | ⟨n, hn, ⟨f⟩⟩
  · exact Or.inl ⟨isClassicalTwoOrG2_of_equiv e h1, fun h => h2 (rankOneChevTwo_of_equiv e.symm h)⟩
  · exact Or.inr ⟨n, hn, ⟨e.symm.trans f⟩⟩

theorem pCoreOf_isPGroup {Y : Type} [Group Y] [Finite Y] (r : ℕ) (hr : r.Prime) (Chat : Subgroup Y) :
    IsPGroup r ↥(CFSG.Open.pCoreOf r Chat) := by
  haveI : Fact r.Prime := ⟨hr⟩
  exact (CFSG.pCore_isPGroup (p := r) (G := ↥Chat)).map Chat.subtype

theorem pCoreOf_normal {Y : Type} [Group Y] [Finite Y] (r : ℕ) (Chat : Subgroup Y) [Chat.Normal] :
    (CFSG.Open.pCoreOf r Chat).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hx
  have h1 : (MulAut.conjNormal (H := Chat) g) a ∈ CFSG.pCore r ↥Chat := by
    have := CFSG.LieType.BorelTits.map_pCore_mulEquiv r (MulAut.conjNormal (H := Chat) g)
    rw [← this]
    exact Subgroup.mem_map_of_mem _ ha
  exact ⟨_, h1, by simp [MulAut.conjNormal_apply]⟩

theorem solvable_centralizer_amb {G : Type} [Group G] [Finite G] (Q V : Subgroup G)
    [Q.Normal] {r : ℕ} (hr : r.Prime) (hQ : IsPGroup r Q)
    (hD : Group.IsSolvable ↥(V ⊓ Subgroup.centralizer (Q : Set G))) :
    Group.IsSolvable ↥((Q ⊔ V) ⊓ Subgroup.centralizer (Q : Set G)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  set C : Subgroup G := Subgroup.centralizer (Q : Set G) with hC
  set D : Subgroup G := V ⊓ C with hDdef
  set T : Subgroup G := V ⊓ (Q ⊔ C) with hT
  have hDT : D ≤ T := inf_le_inf_left _ le_sup_right
  have hTsolv : Group.IsSolvable ↥T := by
    let ρ : G →* MulAut ↥Q := MulAut.conjNormal (H := Q)
    let g : ↥T →* MulAut ↥Q := ρ.comp T.subtype
    let I : Subgroup (MulAut ↥Q) := (ρ.comp Q.subtype).range
    have hI : IsPGroup r ↥I :=
      IsPGroup.of_surjective hQ (ρ.comp Q.subtype).rangeRestrict
        (ρ.comp Q.subtype).rangeRestrict_surjective
    have hcent : ∀ c ∈ C, ρ c = 1 := by
      intro c hc
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      have h1 := (Subgroup.mem_centralizer_iff.1 hc) x.1 x.2
      change c * x.1 * c⁻¹ = x.1
      calc c * x.1 * c⁻¹ = x.1 * c * c⁻¹ := by rw [← h1]
        _ = x.1 := mul_inv_cancel_right _ _
    have hgI : g.range ≤ I := by
      rintro _ ⟨t, rfl⟩
      obtain ⟨q, hq, c, hc, hqc⟩ := Subgroup.mem_sup_of_normal_left.1 t.2.2
      refine ⟨⟨q, hq⟩, ?_⟩
      change ρ q = ρ t.1
      rw [← hqc, map_mul, hcent c hc, mul_one]
    haveI : Group.IsSolvable ↥g.range := by
      haveI := (hI.to_le hgI).isNilpotent
      infer_instance
    let g' : ↥T →* ↥g.range := g.rangeRestrict
    let f : ↥D →* ↥T := Subgroup.inclusion hDT
    refine solvable_of_ker_le_range f g' ?_
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : ρ x.1 = 1 := by
      have := congrArg Subtype.val hx
      exact this
    have hxC : x.1 ∈ C := by
      rw [hC, Subgroup.mem_centralizer_iff]
      intro q hq
      have := congrArg (fun a : MulAut ↥Q => (a ⟨q, hq⟩ : G)) h1
      simp only [MulAut.one_apply] at this
      change x.1 * q * x.1⁻¹ = q at this
      calc q * x.1 = x.1 * q * x.1⁻¹ * x.1 := by rw [this]
        _ = x.1 * q := by group
        
    exact ⟨⟨x.1, x.2.1, hxC⟩, rfl⟩
  set C₀ : Subgroup G := (Q ⊔ V) ⊓ C with hC₀
  let φ : ↥C₀ →* G ⧸ Q := (QuotientGroup.mk' Q).comp C₀.subtype
  haveI hCQ : Group.IsSolvable ↥(C₀ ⊓ Q) := by
    apply Group.isSolvable_of_comm
    intro a b
    apply Subtype.ext
    exact ((Subgroup.mem_centralizer_iff.1 a.2.1.2) b.1 b.2.2).symm
  haveI hrange : Group.IsSolvable ↥φ.range := by
    let ψ : ↥T →* ↥φ.range := ((QuotientGroup.mk' Q).comp T.subtype).codRestrict φ.range (by
      intro t
      obtain ⟨q, hq, c, hc, hqc⟩ := Subgroup.mem_sup_of_normal_left.1 t.2.2
      have hcQV : c ∈ Q ⊔ V := by
        have : c = q⁻¹ * t.1 := by rw [← hqc]; group
        rw [this]
        exact (Q ⊔ V).mul_mem ((Q ⊔ V).inv_mem (Subgroup.mem_sup_left hq)) (Subgroup.mem_sup_right t.2.1)
      refine ⟨⟨c, hcQV, hc⟩, ?_⟩
      change (QuotientGroup.mk' Q) c = (QuotientGroup.mk' Q) t.1
      have hq1 : (QuotientGroup.mk' Q) q = 1 := (QuotientGroup.eq_one_iff q).2 hq
      rw [← hqc, map_mul, hq1, one_mul])
    have hψ : Function.Surjective ψ := by
      rintro ⟨_, ⟨⟨c, hc⟩, rfl⟩⟩
      obtain ⟨q, hq, v, hv, hqv⟩ := Subgroup.mem_sup_of_normal_left.1 hc.1
      have hvT : v ∈ T := ⟨hv, by
        have : v = q⁻¹ * c := by rw [← hqv]; group
        rw [this]
        exact Subgroup.mul_mem_sup (Q.inv_mem hq) hc.2⟩
      refine ⟨⟨v, hvT⟩, ?_⟩
      apply Subtype.ext
      change (QuotientGroup.mk' Q) v = (QuotientGroup.mk' Q) c
      have hq1 : (QuotientGroup.mk' Q) q = 1 := (QuotientGroup.eq_one_iff q).2 hq
      rw [← hqv, map_mul, hq1, one_mul]
    haveI := hTsolv
    exact solvable_of_surjective hψ
  let φ' : ↥C₀ →* ↥φ.range := φ.rangeRestrict
  let f₂ : ↥(C₀ ⊓ Q) →* ↥C₀ := Subgroup.inclusion inf_le_left
  refine solvable_of_ker_le_range f₂ φ' ?_
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h1 : (QuotientGroup.mk' Q) x.1 = 1 := congrArg Subtype.val hx
  exact ⟨⟨x.1, x.2, (QuotientGroup.eq_one_iff _).1 h1⟩, rfl⟩

theorem constrained_quotient {r : ℕ} (hr : r.Prime) {G : Type} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup r Q)
    (hC : Group.IsSolvable ↥(Subgroup.centralizer (Q : Set G))) :
    Subgroup.centralizer (CFSG.pCore r (G ⧸ CFSG.pPrimeCore r G) : Set (G ⧸ CFSG.pPrimeCore r G)) ≤
      CFSG.pCore r (G ⧸ CFSG.pPrimeCore r G) := by
  haveI : Fact r.Prime := ⟨hr⟩
  set K₀ : Subgroup G := CFSG.pPrimeCore r G with hK₀
  haveI hK₀n : K₀.Normal := CFSG.pPrimeCore_normal
  let π : G →* G ⧸ K₀ := QuotientGroup.mk' K₀
  set P : Subgroup (G ⧸ K₀) := CFSG.pCore r (G ⧸ K₀) with hP
  haveI hPn : P.Normal := CFSG.pCore_normal
  set U : Subgroup (G ⧸ K₀) := Subgroup.centralizer (P : Set (G ⧸ K₀)) with hU
  have hQP : Q.map π ≤ P :=
    le_sSup ⟨Subgroup.Normal.map ‹Q.Normal› π (QuotientGroup.mk'_surjective _), hQ.map π⟩
  have hU1 : U.comap π ≤ Subgroup.centralizer (Q : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hcomm : π q * π u = π u * π q :=
      (Subgroup.mem_centralizer_iff.1 hu) (π q) (hQP ⟨q, hq, rfl⟩)
    have hxQ : q * u * q⁻¹ * u⁻¹ ∈ Q := by
      have h1 : u * q⁻¹ * u⁻¹ ∈ Q := by simpa using ‹Q.Normal›.conj_mem q⁻¹ (Q.inv_mem hq) u
      have := Q.mul_mem hq h1
      simpa [mul_assoc] using this
    have hxK : q * u * q⁻¹ * u⁻¹ ∈ K₀ := by
      rw [← QuotientGroup.ker_mk' K₀, MonoidHom.mem_ker]
      change π q * π u * (π q)⁻¹ * (π u)⁻¹ = 1
      rw [hcomm]
      group
    have hcop : Nat.Coprime r (Nat.card K₀) := CFSG.pPrimeCore_coprime_card
    have hx1 : q * u * q⁻¹ * u⁻¹ = 1 := by
      obtain ⟨n, hn⟩ := hQ ⟨_, hxQ⟩
      have h1 : orderOf (q * u * q⁻¹ * u⁻¹) ∣ r ^ n := by
        apply orderOf_dvd_of_pow_eq_one
        exact congrArg Subtype.val hn
      have h2 : orderOf (q * u * q⁻¹ * u⁻¹) ∣ Nat.card K₀ := by
        have := Subgroup.orderOf_dvd_natCard K₀ hxK
        exact this
      have h3 : Nat.Coprime (r ^ n) (Nat.card K₀) := Nat.Coprime.pow_left n hcop
      have := Nat.eq_one_of_dvd_coprimes h3 h1 h2
      exact orderOf_eq_one_iff.1 this
    have : q * u = u * q := by
      have := hx1
      calc q * u = q * u * q⁻¹ * u⁻¹ * (u * q) := by group
        _ = u * q := by rw [hx1, one_mul]
    exact this
  haveI hUn : U.Normal := ⟨fun n hn g => centralizer_conj_mem P hn⟩
  haveI hUs : Group.IsSolvable ↥U := by
    have h1 : Group.IsSolvable ↥(U.comap π) :=
      solvable_of_solvable_injective (f := Subgroup.inclusion hU1) (Subgroup.inclusion_injective hU1)
    have h2 : (U.comap π).map π = U :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective K₀) U
    have h3 : Group.IsSolvable ↥((U.comap π).map π) :=
      solvable_of_surjective (MonoidHom.subgroupMap_surjective π (U.comap π))
    rw [h2] at h3
    exact h3
  have hF : CFSG.fittingSubgroup (G ⧸ K₀) = P :=
    CFSG.Fitting_eq_pcore (G ⧸ K₀) r (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot r)
  set FU : Subgroup ↥U := CFSG.fittingSubgroup ↥U with hFU
  have hFUnormal : (FU.map U.subtype).Normal := by
    refine ⟨fun y hy x => ?_⟩
    obtain ⟨f, hf, rfl⟩ := hy
    have hc := Subgroup.characteristic_iff_map_eq.1 (inferInstance : FU.Characteristic)
      (MulAut.conjNormal (H := U) x)
    have : (MulAut.conjNormal (H := U) x) f ∈ FU := by
      rw [← hc]
      exact Subgroup.mem_map_of_mem _ hf
    exact ⟨_, this, by simp [MulAut.conjNormal_apply]⟩
  have hFUnil : Group.IsNilpotent ↥(FU.map U.subtype) :=
    nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective FU U.subtype U.subtype_injective)
  have hFU_le : FU.map U.subtype ≤ P := by
    rw [← hF]
    exact le_sSup ⟨hFUnormal, hFUnil⟩
  intro u hu
  have hu' : u ∈ U := hu
  have h1 : (⟨u, hu'⟩ : ↥U) ∈ Subgroup.centralizer (FU : Set ↥U) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 hu') f.1 (hFU_le ⟨f, hf, rfl⟩)
  have h2 := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hUs h1
  exact hFU_le ⟨_, h2, rfl⟩

theorem isSubnormal_comap_aux {Y Z : Type} [Group Y] [Group Z] (π : Y →* Z) {A B : Subgroup Z}
    (h : CFSG.Open.IsSubnormal A B) :
    CFSG.Open.IsSubnormal (A.comap π) (B.comap π) := by
  induction h with
  | refl H => exact CFSG.Open.IsSubnormal.refl _
  | @step H M K hHM hnorm hMK ih =>
    refine CFSG.Open.IsSubnormal.step (Subgroup.comap_mono hHM) ?_ ih
    refine ⟨fun n hn g => ?_⟩
    have hnM : π n.1 ∈ M := n.2
    have hgM : π g.1 ∈ M := g.2
    have h1 := hnorm.conj_mem ⟨π n.1, hnM⟩ hn ⟨π g.1, hgM⟩
    change π (g.1 * n.1 * g.1⁻¹) ∈ H
    rw [map_mul, map_mul, map_inv]
    exact h1

theorem isSubnormal_comap {Y Z : Type} [Group Y] [Group Z] (π : Y →* Z) {A : Subgroup Z}
    (h : CFSG.Open.IsSubnormal A ⊤) : CFSG.Open.IsSubnormal (A.comap π) ⊤ := by
  have := isSubnormal_comap_aux π h
  rwa [Subgroup.comap_top] at this

theorem shapeI1_not_alt5 {S : Type} [Group S] (h : ShapeI1 S) :
    ¬ Nonempty (S ≃* alternatingGroup (Fin 5)) := by
  rintro ⟨e⟩
  rcases h with ⟨_, h2⟩ | ⟨n, hn, ⟨f⟩⟩
  · exact h2 (Or.inr ⟨e⟩)
  · have hn2 : 2 ≤ n := by omega
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn2
    have hcard : Nat.card (alternatingGroup (Fin 5)) = Nat.card (alternatingGroup (Fin n)) :=
      Nat.card_congr (e.symm.trans f).toEquiv
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_alternatingGroup,
      card_alternatingGroup] at hcard
    simp only [Fintype.card_fin] at hcard
    rcases hn with rfl | ⟨h8, -⟩
    · norm_num [Nat.factorial] at hcard
    · have h9 : 9 ≤ n := h8
      have := Nat.factorial_le h9
      have h5 : (5 : ℕ).factorial = 120 := by norm_num [Nat.factorial]
      have h9' : (9 : ℕ).factorial = 362880 := by norm_num [Nat.factorial]
      rw [h5] at hcard
      omega

open scoped MatrixGroups in
@[expose] def KListI1 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], ShapeI1 S →
    ¬ Nonempty (S ≃* PSL(3, ZMod 3)) ∧
    ∀ r : ℕ, r.Prime → 5 ≤ r → r ≠ 7 → ¬ Nonempty (S ≃* PSL(2, ZMod r))

theorem isKGroup_barO2 {X : Type} [Group X] [Finite X] (hX : CFSG.IsKGroup X) :
    CFSG.Open.IsKGroup (X ⧸ CFSG.pCore 2 X) :=
  CFSG.HardMathSupport.Solomon.Proving.isKGroup_open_of_catalog (hX.quotient _)

theorem pCore_two_quotient_eq_bot {X : Type} [Group X] [Finite X] :
    CFSG.pCore 2 (X ⧸ CFSG.pCore 2 X) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.GH74.GLS.Stage2.Signalizer.pCore_quotient_pCore 2

theorem three_dvd_card_of_gnThree {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    (h : GNThree T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls) :
    3 ∣ Nat.card (↥Ls ⧸ Subgroup.center ↥Ls) := by
  by_contra hn
  apply (h Ls hLs).1
  have hcop : Nat.Coprime 3 (Nat.card (↥Ls ⧸ Subgroup.center ↥Ls)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hn
  unfold pElementSubgroup
  rw [Subgroup.closure_le]
  rintro x ⟨hxA, k, hk⟩
  have hxL : x ∈ Ls := hxA.2
  refine ⟨⟨x, hxL⟩, ?_, rfl⟩
  set y : ↥Ls := ⟨x, hxL⟩ with hy
  have h1 : y ^ (3 ^ k) = 1 := by
    apply Subtype.ext
    change x ^ (3 ^ k) = 1
    rw [← hk]
    exact pow_orderOf_eq_one x
  have h2 : orderOf (QuotientGroup.mk y : ↥Ls ⧸ Subgroup.center ↥Ls) ∣ 3 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, h1]
    rfl
  have h3 : orderOf (QuotientGroup.mk y : ↥Ls ⧸ Subgroup.center ↥Ls) ∣
      Nat.card (↥Ls ⧸ Subgroup.center ↥Ls) := orderOf_dvd_natCard _
  have h4 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hcop) h2 h3
  have h5 : (QuotientGroup.mk y : ↥Ls ⧸ Subgroup.center ↥Ls) = 1 := orderOf_eq_one_iff.1 h4
  exact (QuotientGroup.eq_one_iff y).1 h5

theorem shapeI1_of_gnShape {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    (h : GNShape T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls) :
    ShapeI1 (↥Ls ⧸ Subgroup.center ↥Ls) := by
  obtain ⟨-, hsh⟩ := h Ls hLs
  rcases hsh with h1 | ⟨n, hn, ⟨f⟩⟩
  · exact Or.inl h1
  · have hn4 : 4 ≤ n := by rcases hn with h | ⟨h, _⟩ <;> omega
    have hcard : 4 ≤ Nat.card (Fin n) := by simpa using hn4
    have hZ : Subgroup.center ↥Ls = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have h2 : f z ∈ Subgroup.center (alternatingGroup (Fin n)) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h3 := congrArg f ((Subgroup.mem_center_iff.1 hz) (f.symm g))
        simpa using h3
      rw [alternatingGroup.center_eq_bot hcard, Subgroup.mem_bot] at h2
      have : z = 1 := f.injective (by rw [h2, map_one])
      simp [this]
    have e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* alternatingGroup (Fin n) :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans f
    exact Or.inr ⟨n, hn, ⟨e⟩⟩

theorem pRank_top_bar_le {G : Type} [Group G] [Finite G] (M : Subgroup G) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ CFSG.Open.pRank r M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : ¬ r ∣ Nat.card (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).ker := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hn]
    intro h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  have hbar := CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hr
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) hker ⊤
  rw [Subgroup.map_top, MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    at hbar
  have hM : CFSG.Open.pRank r (⊤ : Subgroup ↥M) = CFSG.Open.pRank r M :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := r) M).symm
  exact hbar.trans hM.le

theorem exists_perfect_cover {Y Z : Type} [Group Y] [Finite Y] [Group Z] (π : Y →* Z)
    (hπ : Function.Surjective π) (Ls : Subgroup Z) (hLs : CFSG.Open.IsComponentOf Ls ⊤) :
    ∃ E : Subgroup Y, ⁅E, E⁆ = E ∧ E.map π = Ls := by
  let f : Subgroup Y → Subgroup Y := fun H => ⁅H, H⁆
  let a : ℕ → Subgroup Y := fun n => f^[n] (Ls.comap π)
  have hfle : ∀ H, f H ≤ H := fun H => Subgroup.commutator_le_of_le (le_refl H) (le_refl H)
  have hsucc : ∀ n, a (n + 1) = f (a n) := fun n => Function.iterate_succ_apply' f n _
  have hanti : ∀ n, a (n + 1) ≤ a n := fun n => by rw [hsucc]; exact hfle _
  have hmap : ∀ n, (a n).map π = Ls := by
    intro n
    induction n with
    | zero => exact Subgroup.map_comap_eq_self_of_surjective hπ Ls
    | succ n ih =>
      rw [hsucc]
      change (⁅a n, a n⁆).map π = Ls
      rw [Subgroup.map_commutator, ih]
      exact commutator_eq_self_of_isQuasisimple hLs.2.2
  obtain ⟨m, k, hmk, hk⟩ := Finite.exists_ne_map_eq_of_infinite a
  have hanti' : Antitone a := antitone_nat_of_succ_le hanti
  have hstab : ∃ n, a (n + 1) = a n := by
    rcases lt_or_gt_of_ne hmk with h | h
    · exact ⟨m, le_antisymm (hanti m) (hk ▸ hanti' (Nat.succ_le_of_lt h))⟩
    · exact ⟨k, le_antisymm (hanti k) (hk.symm ▸ hanti' (Nat.succ_le_of_lt h))⟩
  obtain ⟨n, hn⟩ := hstab
  exact ⟨a n, (hsucc n).symm.trans hn, hmap n⟩

theorem hloc_of_ctx {G : Type} [Group G] [Finite G] {M T : Subgroup G} (hcyc : CycHat G M T) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) :
    IsCyclic ↥(CFSG.Open.pCoreOf r
      ((gnC (T.subgroupOf M)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)))) ∨ r = 3 := by
  by_cases h3 : r = 3
  · exact Or.inr h3
  · refine Or.inl (hcyc r hr ?_)
    have h2 := hr.two_le
    rcases (show r = 4 ∨ 5 ≤ r by omega) with h4 | h
    · subst h4
      norm_num at hr
    · omega

end CFSG.LocalAnalysis.RankThreeUC.S15
