module

public import CFSG.ClassicalInvolution.Q3.TL3T57
public import CFSG.ClassicalInvolution.Q3.TL3T52A

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

namespace CHyp

variable {K J : Subgroup G} (hS : CHyp 3 IH Ω K J)
include hS

theorem exists_data128_of {n : ℕ} (hn : 5 ≤ n) (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n)
    {g : G} (hg : conjSub g K = J) :
    ∃ Ks : Subgroup G, ∃ y : G, Data128 Ω K J g Ks y ∧
      ∃ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool)
        (y₀ : ↥(pSpan (orbOf (TC.nbrAdj Ω) K J))), I.φ y₀ = AE.yBar α h ∧
        (y₀ : G) = g⁻¹ * y * g ∧ conjSub g⁻¹ K ∈ orbOf (TC.nbrAdj Ω) K J ∧
        conjSub g⁻¹ Ks ∈ orbOf (TC.nbrAdj Ω) K J ∧
        ((conjSub g⁻¹ K).subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ =
          AE.memBar α h b ∧
        ((conjSub g⁻¹ Ks).subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ =
          AE.memBar α h (!b) := by
  classical
  revert I
  set π := orbOf (TC.nbrAdj Ω) K J with hπ
  intro I
  have hF := hS.graphFam'
  have hK : K ∈ Ω := hS.adj.1
  have hJπ : J ∈ π := mem_orbOf_self K J
  have hJΩ : J ∈ Ω := hS.orb_subset_omega hJπ
  have h8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hS.card L hL]; norm_num
  have hgπ : conjSub g K ∈ π := hg ▸ hJπ
  obtain ⟨L₀, hL₀, hL₀K⟩ := hS.mem_conj_orb hgπ
  have hPΩ : π ⊆ Ω := hS.orb_subset_omega
  have hinv : ∀ L ∈ π, ∀ x ∈ pSpan π, conjSub x L ∈ π := fun L hL x hx =>
    CSetting.conjSub_mem_orb hK (hS.pSpan_orb_le hx) hL
  have hk : IsPGroup 2 I.φ.ker := I.toLabel.isPGroup_ker hS.oddCore_orb_eq_bot
  obtain ⟨α, h, b, hlab⟩ := I.label L₀ hL₀
  obtain ⟨L₁, hL₁, hlab₁⟩ := I.label_surj α h (!b)
  obtain ⟨y₀, hy₀, ⟨a, hy₀pow⟩, hy₀z, hy₀L⟩ := I.exists_y hS.hyp hS.two hPΩ hinv hn hk hL₀ hlab
  have hy₀L₁ := I.conjSub_eq_of_map_eq_yBar hS.hyp hS.two hPΩ hinv hn hk hL₁ hlab₁ hy₀
  have hne : AE.memBar α h b ≠ AE.memBar α h (!b) := by
    cases b
    · exact (AE.memBar_true_ne_false hn α h).symm
    · exact AE.memBar_true_ne_false hn α h
  have hL₀₁ : L₀ ≠ L₁ := fun e => hne (by rw [← hlab, ← hlab₁, e])
  have hcomm₀ : ∀ x ∈ L₀, ∀ y ∈ L₁, x * y = y * x :=
    aeIdent_comm_of_map_comm hS.hyp hS.two hPΩ I hk hL₀ hL₁ hL₀₁
      (by rw [hlab, hlab₁]; exact memBar_twin_comm α h b)
  have hKL₀ : conjSub g⁻¹ K = L₀ := by rw [← hL₀K, conjSub_inv_conjSub]
  have hy₀pow' : (y₀ : G) ^ 3 ^ a = 1 := by
    have := congrArg Subtype.val hy₀pow
    rwa [Subgroup.coe_pow] at this
  have hJK : TC.nbrAdj Ω J K := hF.graph.symm hS.adj
  have horbg : conjSub g '' π = orbOf (TC.nbrAdj Ω) J K := by
    rw [hS.conj_orb_eq hgπ, hg]
  have hpg : ∀ x ∈ pSpan π, g * x * g⁻¹ ∈ pSpan (conjSub g '' π) := fun x hx => by
    have := (pSpanConj g π ⟨x, hx⟩).2
    rwa [pSpanConj_apply] at this
  have hXgJ : pSpan (conjSub g '' π) ≤ Subgroup.centralizer (J : Set G) := by
    rw [horbg]
    refine (pSpan_le fun L hL => le_pSpan (adj_of_mem_orbOf hF.graph hJK hL).2).trans ?_
    exact pSpan_omegaNbr_le_centralizer hS.hyp hS.two hJΩ
  refine ⟨conjSub g L₁, g * y₀ * g⁻¹, ⟨hg, ⟨L₁, hL₁, rfl⟩, ?_, ?_, ⟨a, ?_⟩, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩, α, h, b, y₀, hy₀, by group, hKL₀ ▸ hL₀, by rw [conjSub_inv_conjSub]; exact hL₁,
    by rw [hKL₀]; exact hlab, by rw [conjSub_inv_conjSub]; exact hlab₁⟩
  ·
    intro e
    exact hL₀₁ (conjSub_injective g (hL₀K.trans e.symm))
  ·
    rw [← hL₀K]
    exact comm_conjSub hcomm₀ g
  · rw [conj_pow, hy₀pow', mul_one, mul_inv_cancel]
  · exact hpg _ y₀.2
  ·
    intro z hz
    have hz' : IsUniqueInvolution L₀ (g⁻¹ * z * g⁻¹⁻¹) := hKL₀ ▸ hz.conj g⁻¹
    have e := hy₀z _ hz'
    calc g * y₀ * g⁻¹ * z = g * ((y₀ : G) * (g⁻¹ * z * g⁻¹⁻¹)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g⁻¹⁻¹) * (y₀ : G)) * g⁻¹ := by rw [e]
      _ = z * (g * y₀ * g⁻¹) := by group
  ·
    rw [← hL₀K, conjSub_mul, conjSub_mul, conjSub_inv_conjSub, hy₀L]
  · rw [conjSub_mul, conjSub_mul, conjSub_inv_conjSub, hy₀L₁]
  ·
    intro hc
    obtain ⟨x, hx, hxne⟩ := AE.yBar_not_comm_memBar hn α h b
    rw [← hlab] at hx
    obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map hL₀ hx
    apply hxne
    rw [← hy₀, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    have hgl : g * l * g⁻¹ ∈ K := hL₀K ▸ conj_mem_conjSub hl
    have e := hc _ hgl
    show (y₀ : G) * l = l * y₀
    calc (y₀ : G) * l = g⁻¹ * ((g * y₀ * g⁻¹) * (g * l * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * l * g⁻¹) * (g * y₀ * g⁻¹)) * g := by rw [e]
      _ = l * y₀ := by group
  ·
    intro hc
    obtain ⟨x, hx, hxne⟩ := AE.yBar_not_comm_memBar hn α h (!b)
    rw [← hlab₁] at hx
    obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map hL₁ hx
    apply hxne
    rw [← hy₀, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    have hgl : g * l * g⁻¹ ∈ conjSub g L₁ := conj_mem_conjSub hl
    have e := hc _ hgl
    show (y₀ : G) * l = l * y₀
    calc (y₀ : G) * l = g⁻¹ * ((g * y₀ * g⁻¹) * (g * l * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * l * g⁻¹) * (g * y₀ * g⁻¹)) * g := by rw [e]
      _ = l * y₀ := by group
  ·
    intro M hMπ hMperp hMKs m hm
    have hy : g * y₀ * g⁻¹ ∈ pSpan (conjSub g '' π) := hpg _ y₀.2
    rcases Set.mem_insert_iff.mp hMperp with rfl | hMJ
    · exact ((Subgroup.mem_centralizer_iff.mp (hXgJ hy)) m hm).symm
    · by_cases hMg : M ∈ conjSub g '' π
      · obtain ⟨M', hM', rfl⟩ := hMg
        have hMK : ∀ x ∈ K, ∀ y ∈ conjSub g M', x * y = y * x :=
          comm_of_mem_omegaNbr hS.hyp hS.two hK (hS.orb_subset hMπ)
        have hM'L₀ : ∀ x ∈ L₀, ∀ y ∈ M', x * y = y * x := by
          have := comm_conjSub hMK g⁻¹
          rwa [hKL₀, conjSub_inv_conjSub] at this
        obtain ⟨β, h', c, hlab'⟩ := I.label M' hM'
        have hc : ∀ x ∈ AE.memBar α h b, ∀ y ∈ AE.memBar β h' c, x * y = y * x := by
          rw [← hlab, ← hlab']
          rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (hM'L₀ _ (Subgroup.mem_subgroupOf.mp hu) _
            (Subgroup.mem_subgroupOf.mp hv))
        rcases eq_or_disjoint_of_comm hc with hαβ | hd
        · exfalso
          subst hαβ
          have hcb : c = b ∨ c = !b := by cases b <;> cases c <;> simp
          rcases hcb with rfl | rfl
          · have := aeIdent_eq_of_map_eq hS.hyp hS.two hPΩ hn I hk hL₀ hM' (hlab.trans hlab'.symm)
            subst this
            rw [hL₀K] at hMπ
            exact (hS.orb_subset hMπ).2.1 rfl
          · have := aeIdent_eq_of_map_eq hS.hyp hS.two hPΩ hn I hk hL₁ hM'
              (hlab₁.trans hlab'.symm)
            subst this
            exact hMKs rfl
        · have hm' : g⁻¹ * m * g ∈ M' := by
            have := mem_conjSub_iff.mp hm
            simpa using this
          set w : ↥(pSpan π) := ⟨g⁻¹ * m * g, le_pSpan hM' hm'⟩ with hw
          have hcw : I.toLabel.φ y₀ * I.toLabel.φ w = I.toLabel.φ w * I.toLabel.φ y₀ := by
            show I.φ y₀ * I.φ w = I.φ w * I.φ y₀
            rw [hy₀]
            exact AE.yBar_comm_memBar_of_disjoint hd c _ (by rw [← hlab']; exact I.mem_map hM' hm')
          have e := congrArg Subtype.val (I.toLabel.comm_of_pow_three hk hy₀pow hcw)
          change (y₀ : G) * (g⁻¹ * m * g) = (g⁻¹ * m * g) * y₀ at e
          calc g * y₀ * g⁻¹ * m = g * ((y₀ : G) * (g⁻¹ * m * g)) * g⁻¹ := by group
            _ = g * ((g⁻¹ * m * g) * (y₀ : G)) * g⁻¹ := by rw [e]
            _ = m * (g * y₀ * g⁻¹) := by group
      ·
        have hJM : TC.nbrAdj Ω J M := ⟨hJΩ, hMJ⟩
        have hle : pSpan (conjSub g '' π) ≤ Subgroup.centralizer (M : Set G) := by
          rw [horbg]
          refine pSpan_le fun N hN => ?_
          have hJN : TC.nbrAdj Ω J N := adj_of_mem_orbOf hF.graph hJK hN
          have hnot : M ∉ orbOf (TC.nbrAdj Ω) J N := by
            rw [orbOf_eq_of_mem hN, ← horbg]
            exact hMg
          have hNM := hS.sepHyp hJN hJM hnot
          intro x hx
          exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
            (comm_of_mem_omegaNbr hS.hyp hS.two hNM.1 hNM.2 x hx y hy).symm
        exact ((Subgroup.mem_centralizer_iff.mp (hle hy)) m hm).symm
  ·
    intro z zs hz hzs x hx
    have hz' : IsUniqueInvolution L₀ (g⁻¹ * z * g⁻¹⁻¹) := hKL₀ ▸ hz.conj g⁻¹
    have hzs' : IsUniqueInvolution L₁ (g⁻¹ * zs * g⁻¹⁻¹) := by
      have := hzs.conj g⁻¹
      rwa [conjSub_inv_conjSub] at this
    have e1 := I.map_eq_zBar hn hL₀ (h8 L₀ (hPΩ hL₀)) hlab hz'
    have e2 := I.map_eq_zBar hn hL₁ (h8 L₁ (hPΩ hL₁)) hlab₁ hzs'
    set w : ↥(pSpan π) := ⟨g⁻¹ * zs * g⁻¹⁻¹, le_pSpan hL₁ hzs'.mem⟩ *
      ⟨g⁻¹ * z * g⁻¹⁻¹, le_pSpan hL₀ hz'.mem⟩ with hw
    have hwk : w ∈ I.φ.ker := by
      rw [MonoidHom.mem_ker, hw, map_mul, e1, e2, AE.zBar_mul_self]
    have hwc := Subgroup.mem_center_iff.mp (I.ker_le hwk)
    have hx₀ : g⁻¹ * x * g ∈ pSpan π := by
      have := ((pSpanConj g π).symm ⟨x, hx⟩).2
      rwa [pSpanConj_symm_apply] at this
    have e := congrArg Subtype.val (hwc ⟨g⁻¹ * x * g, hx₀⟩)
    change (g⁻¹ * x * g) * ((g⁻¹ * zs * g⁻¹⁻¹) * (g⁻¹ * z * g⁻¹⁻¹)) =
      ((g⁻¹ * zs * g⁻¹⁻¹) * (g⁻¹ * z * g⁻¹⁻¹)) * (g⁻¹ * x * g) at e
    calc x * (zs * z) = g * ((g⁻¹ * x * g) * ((g⁻¹ * zs * g⁻¹⁻¹) * (g⁻¹ * z * g⁻¹⁻¹))) * g⁻¹ := by
          group
      _ = g * (((g⁻¹ * zs * g⁻¹⁻¹) * (g⁻¹ * z * g⁻¹⁻¹)) * (g⁻¹ * x * g)) * g⁻¹ := by rw [e]
      _ = zs * z * x := by group

private theorem twin_props {n : ℕ} (hn : 5 ≤ n) (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n)
    {g : G} {Ks : Subgroup G} {y : G} (hD : Data128 Ω K J g Ks y) {α : Finset (Fin n)}
    {h : α.card = 4} {b : Bool} {y₀ : ↥(pSpan (orbOf (TC.nbrAdj Ω) K J))}
    (hy₀ : I.φ y₀ = AE.yBar α h) (hy₀y : (y₀ : G) = g⁻¹ * y * g)
    (hlab₀ : ((conjSub g⁻¹ K).subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ =
      AE.memBar α h b)
    (hlab₁ : ((conjSub g⁻¹ Ks).subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ =
      AE.memBar α h (!b)) :
    (∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), y * x = x * y) ∧
      Ks ∈ omegaNbr Ω K ∧ Ks ∉ orbOf (TC.nbrAdj Ω) K J ∧
      (∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x) ∧
      ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z := by
  have hy : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), y * x = x * y := by
    rcases eq_or_ne n 7 with rfl | hn7
    · exact hS.y_comm_seven I hD hy₀ hy₀y hlab₀ hlab₁
    · exact hS.y_comm_of_rigid hn I (ae3Rigid hn hn7) hD
  obtain ⟨hKsK, hKsπ, hKs⟩ := hS.ks_comm_of_y_comm hD hy
  exact ⟨hy, hKsK, hKsπ, hKs, fun z zs hz hzs => hS.z_eq_of_ks_comm hD hKs hz hzs⟩

theorem exists_twin_at_J_label {n : ℕ} (hn : 5 ≤ n) (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n)
    {γ : Finset (Fin n)} {hγ : γ.card = 4} {c : Bool}
    (hlabJ : (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = AE.memBar γ hγ c) :
    ∃ Js ∈ orbOf (TC.nbrAdj Ω) K J, Js ≠ J ∧ (∀ a ∈ J, ∀ b ∈ Js, a * b = b * a) ∧
      (∀ z zs : G, IsUniqueInvolution J z → IsUniqueInvolution Js zs → zs = z) ∧
      (Js.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = AE.memBar γ hγ (!c) := by
  obtain ⟨t, ht, ht'⟩ := hS.exists_swap
  obtain ⟨Ks, y, hD, α, h, b, y₀, hy₀, hy₀y, -, hL₁π, hlab₀, hlab₁⟩ :=
    hS.exists_data128_of hn I ht
  obtain ⟨-, -, -, -, hz⟩ := hS.twin_props hn I hD hy₀ hy₀y hlab₀ hlab₁
  have hKJ : conjSub t⁻¹ K = J := by rw [← ht', conjSub_inv_conjSub]
  rw [hKJ] at hlab₀
  have hαγ : α = γ := AE.eq_of_memBar_eq' hn (hlab₀.symm.trans hlabJ)
  subst hαγ
  have hbc : b = c := by
    by_contra hne
    have hc : c = !b := by cases b <;> cases c <;> first | rfl | exact absurd rfl hne
    subst hc
    cases b
    · exact AE.memBar_true_ne_false hn _ _ (hlab₀.symm.trans hlabJ).symm
    · exact AE.memBar_true_ne_false hn _ _ (hlab₀.symm.trans hlabJ)
  subst hbc
  refine ⟨conjSub t⁻¹ Ks, hL₁π, fun e => hD.Ks_ne (conjSub_injective t⁻¹ (e.trans hKJ.symm)),
    ?_, ?_, hlab₁⟩
  · rw [← hKJ]
    exact comm_conjSub hD.comm t⁻¹
  · intro z zs hz' hzs'
    have h1 : IsUniqueInvolution K (t * z * t⁻¹) := ht' ▸ hz'.conj t
    have h2 : IsUniqueInvolution Ks (t * zs * t⁻¹) := by
      have := hzs'.conj t
      rwa [conjSub_conjSub_inv] at this
    exact mul_left_cancel (mul_right_cancel (hz _ _ h1 h2))

private theorem chyp_of_mem {L : Subgroup G} (hL : L ∈ orbOf (TC.nbrAdj Ω) K J) :
    CHyp 3 IH Ω K L where
  toCHypG := hS.toCHypG
  adj := adj_of_mem_orbOf hS.graphFam'.graph hS.adj hL
  max := by rw [orbOf_eq_of_mem hL]; exact hS.max

theorem z_eq_of_label' {n : ℕ} (hn : 5 ≤ n) (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n)
    {L L' : Subgroup G} (hL : L ∈ orbOf (TC.nbrAdj Ω) K J) (hL' : L' ∈ orbOf (TC.nbrAdj Ω) K J)
    {δ : Finset (Fin n)} {hδ hδ' : δ.card = 4} {d d' : Bool}
    (hlab : (L.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = AE.memBar δ hδ d)
    (hlab' : (L'.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = AE.memBar δ hδ' d') :
    ∀ z z' : G, IsUniqueInvolution L z → IsUniqueInvolution L' z' → z' = z := by
  intro z z' hz hz'
  have key : ∀ P : Set (Subgroup G), orbOf (TC.nbrAdj Ω) K L = P → ∀ I' : AEIdent P n,
      (L.subgroupOf (pSpan P)).map I'.φ = AE.memBar δ hδ d →
      ∃ Ls ∈ P, (∀ z zs : G, IsUniqueInvolution L z → IsUniqueInvolution Ls zs → zs = z) ∧
        (Ls.subgroupOf (pSpan P)).map I'.φ = AE.memBar δ hδ (!d) := by
    rintro P rfl I' hlab''
    obtain ⟨Ls, hLs, -, -, hzs, hlabs⟩ := (hS.chyp_of_mem hL).exists_twin_at_J_label hn I' hlab''
    exact ⟨Ls, hLs, hzs, hlabs⟩
  obtain ⟨Ls, hLs, hzs, hlabs⟩ := key _ (orbOf_eq_of_mem hL) I hlab
  have heq : ∀ {M M' : Subgroup G}, M ∈ orbOf (TC.nbrAdj Ω) K J →
      M' ∈ orbOf (TC.nbrAdj Ω) K J →
      (M.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ =
        (M'.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ → M = M' :=
    fun hM hM' h => aeIdent_eq_of_map_eq hS.hyp hS.two hS.orb_subset_omega hn I
      (I.toLabel.isPGroup_ker hS.oddCore_orb_eq_bot) hM hM' h
  have hd' : d' = d ∨ d' = !d := by cases d <;> cases d' <;> simp
  rcases hd' with rfl | rfl
  · obtain rfl : L' = L := heq hL' hL (hlab'.trans hlab.symm)
    exact hz'.eq hz
  · obtain rfl : L' = Ls := heq hL' hLs (hlab'.trans hlabs.symm)
    exact hzs z z' hz hz'

theorem aeCoverHyp_orb' {n : ℕ} (hn : 5 ≤ n) (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) :
    TL4.AECoverHyp I where
  ker_two := I.toLabel.isPGroup_ker hS.oddCore_orb_eq_bot
  card := fun L hL => by rw [hS.card L (hS.orb_subset_omega hL)]; norm_num
  conj_mem := fun L hL x hx => CSetting.conjSub_mem_orb hS.adj.1 (hS.pSpan_orb_le hx) hL
  label_inj := fun L hL L' hL' h => aeIdent_eq_of_map_eq hS.hyp hS.two hS.orb_subset_omega hn I
    (I.toLabel.isPGroup_ker hS.oddCore_orb_eq_bot) hL hL' h
  twin_comm := by
    intro α h L hL L' hL' hlab hlab'
    refine aeIdent_comm_of_map_comm hS.hyp hS.two hS.orb_subset_omega I
      (I.toLabel.isPGroup_ker hS.oddCore_orb_eq_bot) hL hL' ?_ ?_
    · intro e
      subst e
      rw [hlab] at hlab'
      exact AE.memBar_true_ne_false hn α h hlab'
    · rw [hlab, hlab']
      exact memBar_twin_comm α h true
  twin_z := by
    intro α h L hL L' hL' hlab hlab' u u' hu hu'
    exact (hS.z_eq_of_label' hn I hL hL' hlab hlab' u u' hu hu').symm

end CHyp

theorem CSetting.swap {K J : Subgroup G} (hS : CSetting 3 IH Ω K J) : CSetting 3 IH Ω J K where
  cex := hS.cex
  center := hS.center
  conn := hS.conn
  d1 := hS.d1
  adj := hS.toCHyp.swap.adj
  max := hS.toCHyp.swap.max

end CFSG.ClassicalInvolution.Q3.TC.Thin
