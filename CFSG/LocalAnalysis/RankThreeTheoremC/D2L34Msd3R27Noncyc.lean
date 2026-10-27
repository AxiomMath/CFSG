module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27TwoEsc
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WNoncycD
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27NoncycFF
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27NoncycN

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim

variable {G : Type} [Group G] [Finite G]

section Ctx

variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {T : Subgroup G}

private theorem D2L34R27.eq_of_le_centralizer (c : D2L34R27 G d P M A H R Rbar K T)
    {N X E : Subgroup G} (hN2 : IsTwoLocal N) (hNM : ¬ N ≤ M) (hXN : X ≤ N) (hXM : X ≤ M)
    (hX : IsPGroup 3 X) (hEX : E ≤ X) (hEel : IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEcore : GLBCore 3 1 E ≤ M) (hXC : X ≤ Subgroup.centralizer (E : Set G)) : X = E := by
  rcases c.eq_or_extraspecial_of_good hN2 hNM hXN hXM hX hEX hEel hE9 hEcore with h | ⟨-, hes⟩
  · exact h
  · exfalso
    have hle : E.subgroupOf X ≤ Subgroup.center ↥X := by
      intro e he
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext
        (Subgroup.mem_centralizer_iff.mp (hXC y.2) e (Subgroup.mem_subgroupOf.mp he)).symm
    have h1 := Subgroup.card_le_of_le hle
    rw [hes.2.2.2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv, hE9] at h1
    omega

private theorem le_centralizer_of_sylow {N U CN E Q : Subgroup G} (hUN : U ≤ N)
    (hUp : IsPGroup 3 U) (hUidx : ¬ 3 ∣ (U.subgroupOf N).index)
    (hUC : U ≤ Subgroup.centralizer (E : Set G)) (hNCN : N ≤ Subgroup.normalizer (CN : Set G))
    (hECN : E ≤ CN) (hUCN : U ⊓ CN = E) (hQN : Q ≤ N) (hQp : IsPGroup 3 Q) (hEQ : E ≤ Q) :
    Q ≤ Subgroup.centralizer (E : Set G) := by
  obtain ⟨g, hgN, hgQ⟩ := exists_conj_map_le_of_isPGroup hUN hUp hUidx hQN hQp
  have hEg : E.map (MulAut.conj g).toMonoidHom ≤ U ⊓ CN := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hgQ ⟨x, hEQ hx, rfl⟩, (Subgroup.mem_normalizer_iff.1 (hNCN hgN) x).1 (hECN hx)⟩
  rw [hUCN] at hEg
  have hEgE : E.map (MulAut.conj g).toMonoidHom = E :=
    Subgroup.eq_of_le_of_card_ge hEg
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have h1 : g * q * g⁻¹ ∈ Subgroup.centralizer (E : Set G) := hUC (hgQ ⟨q, hq, rfl⟩)
  have h2 : g * e * g⁻¹ ∈ E := by
    rw [← hEgE]
    exact ⟨e, he, rfl⟩
  have h3 := Subgroup.mem_centralizer_iff.1 h1 _ h2
  calc e * q = g⁻¹ * ((g * e * g⁻¹) * (g * q * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * q * g⁻¹) * (g * e * g⁻¹)) * g := by rw [h3]
    _ = q * e := by group

private theorem D2L34R27.comm_of_factorization
    (c : D2L34R27 G d P M A H R Rbar K T) {Z X₂ N U CN B E : Subgroup G}
    (hZ1 : Z ≠ ⊥) (hZ2 : IsPGroup 2 Z)
    (hZT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (Z : Set G))
    (hX₂1 : X₂ ≠ ⊥) (hX₂2 : IsPGroup 2 X₂)
    (hX₂T : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₂ : Set G))
    (hNM : N ≤ M) (hUN : U ≤ N) (hUp : IsPGroup 3 U) (hUidx : ¬ 3 ∣ (U.subgroupOf N).index)
    (hU27 : 27 ≤ Nat.card U) (hEU : E ≤ U) (hUC : U ≤ Subgroup.centralizer (E : Set G))
    (hEel : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hEcore : GLBCore 3 1 E ≤ M)
    (hCNN : CN ≤ N) (hNCN : N ≤ Subgroup.normalizer (CN : Set G))
    (hCNZ : CN ≤ Subgroup.normalizer (Z : Set G)) (hECN : E ≤ CN) (hUCN : U ⊓ CN = E)
    (hBN : B ≤ N) (hBX : B ≤ Subgroup.normalizer (X₂ : Set G))
    (hfac : ∀ n ∈ N, ∃ c ∈ CN, ∃ b ∈ B, n = c * b) :
    ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZloc : IsTwoLocal (Subgroup.normalizer (Z : Set G)) := ⟨Z, hZ1, hZ2, rfl⟩
  have hZM : ¬ Subgroup.normalizer (Z : Set G) ≤ M := fun h => c.not_normalizer_le (hZT.trans h)
  have hX₂loc : IsTwoLocal (Subgroup.normalizer (X₂ : Set G)) := ⟨X₂, hX₂1, hX₂2, rfl⟩
  have hX₂M : ¬ Subgroup.normalizer (X₂ : Set G) ≤ M := fun h =>
    c.not_normalizer_le (hX₂T.trans h)
  obtain ⟨W', W₂, hW'N, hW'p, hW'idx, hW₂B, hW₂W', hW'fac⟩ :=
    exists_sylow_of_normal_mul hCNN hNCN hBN hfac
  obtain ⟨g, hgN, hgU⟩ := exists_conj_map_le_of_isPGroup hW'N hW'p hW'idx hUN hUp
  obtain ⟨g', -, hg'W'⟩ := exists_conj_map_le_of_isPGroup hUN hUp hUidx hW'N hW'p
  have hcardU : Nat.card (U.map (MulAut.conj g).toMonoidHom) = Nat.card U :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hcardW' : Nat.card (W'.map (MulAut.conj g').toMonoidHom) = Nat.card W' :=
    Subgroup.card_map_of_injective (MulAut.conj g').injective
  have hUW' : U.map (MulAut.conj g).toMonoidHom = W' :=
    Subgroup.eq_of_le_of_card_ge hgU (by have := Subgroup.card_le_of_le hg'W'; omega)
  have hgM : g ∈ M := hNM hgN
  set E' : Subgroup G := E.map (MulAut.conj g).toMonoidHom with hE'def
  have hE'el : IsElemAbelian 3 E' := elementary_abelian_map 3 hEel _
  have hE'9 : Nat.card E' = 9 := by
    rw [hE'def, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE9]
  have hE'core : GLBCore 3 1 E' ≤ M := glbCore_one_map_conj_le hgM hEcore
  have hE'W' : E' ≤ W' := hUW' ▸ Subgroup.map_mono hEU
  have hE'CN : E' ≤ CN := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (hNCN hgN) x).1 (hECN hx)
  have hE'M : E' ≤ M := hE'CN.trans (hCNN.trans hNM)
  have hW'M : W' ≤ M := hW'N.trans hNM
  have hW'C : W' ≤ Subgroup.centralizer (E' : Set G) := by
    rw [← hUW']
    rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨e, he, rfl⟩
    have h := Subgroup.mem_centralizer_iff.1 (hUC hu) e he
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * e * g⁻¹ * (g * u * g⁻¹) = g * (e * u) * g⁻¹ := by group
      _ = g * (u * e) * g⁻¹ := by rw [h]
      _ = g * u * g⁻¹ * (g * e * g⁻¹) := by group
  have hW'CN : W' ⊓ CN = E' :=
    c.eq_of_le_centralizer hZloc hZM (inf_le_right.trans hCNZ) (inf_le_left.trans hW'M)
      (hW'p.to_le inf_le_left) (le_inf hE'W' hE'CN) hE'el hE'9 hE'core (inf_le_left.trans hW'C)
  have hW₂p : IsPGroup 3 W₂ := hW'p.to_le hW₂W'
  have hW₂cyc : IsCyclic ↥W₂ := by
    by_contra hnc
    obtain ⟨R₀, hR₀W₂, hR₀el, hR₀9⟩ := exists_E9_le_of_not_isCyclic hW₂p hnc
    have hR₀W' : R₀ ≤ W' := hR₀W₂.trans hW₂W'
    have hR₀M : R₀ ≤ M := hR₀W'.trans hW'M
    have hR₀X : R₀ ≤ Subgroup.normalizer (X₂ : Set G) := hR₀W₂.trans (hW₂B.trans hBX)
    by_cases hR₀E : R₀ = E'
    ·
      have hW'W₂ : W' ≤ W₂ := by
        intro w hw
        obtain ⟨a, ha, b, hb, rfl⟩ := hW'fac w hw
        rw [hW'CN, ← hR₀E] at ha
        exact W₂.mul_mem (hR₀W₂ ha) hb
      have hW'E : W' = E' :=
        c.eq_of_le_centralizer hX₂loc hX₂M (hW'W₂.trans (hW₂B.trans hBX)) hW'M hW'p hE'W' hE'el
          hE'9 hE'core hW'C
      have hcW' : Nat.card W' = Nat.card U := by rw [← hUW', hcardU]
      rw [hW'E, hE'9] at hcW'
      omega
    ·
      obtain ⟨F, hFle, hFel, hF27, hFcomm⟩ := exists_E27_of_commuting_E9 hE'el hE'9 hR₀el hR₀9
        (fun h => hR₀E h.symm) fun e he r hr =>
          Subgroup.mem_centralizer_iff.mp (hW'C (hR₀W' hr)) e he
      have hFM : F ≤ M := hFle.trans (sup_le hE'M hR₀M)
      have hgR₀ : HasGoodE9 M R₀ :=
        c.ctx.hasGoodE9_of_centralizes le_rfl hR₀M hR₀el hR₀9 hFM hFel hF27 hFcomm
      have hgE' : HasGoodE9 M E' := ⟨E', le_rfl, hE'el, hE'9, hE'core⟩
      have h3 : 3 ≤ CFSG.Open.pRank 3 (E' ⊔ R₀ : Subgroup G) :=
        CFSG.SectionRank.le_pRank Nat.prime_three.one_lt hFle hFel (by rw [hF27]; norm_num)
      exact c.false_of_two_escapes hZ1 hZ2 hZT hX₂1 hX₂2 hX₂T
        (le_inf hE'M (hE'CN.trans hCNZ)) (le_inf hR₀M hR₀X) (hW'p.to_le hE'W')
        (hW'p.to_le hR₀W') hgE' hgR₀ (hW'p.to_le (sup_le hE'W' hR₀W')) h3
  have hW₂comm : ∀ y ∈ W₂, ∀ y' ∈ W₂, y * y' = y' * y := fun y hy y' hy' =>
    congrArg Subtype.val ((IsCyclic.commGroup (α := W₂)).mul_comm ⟨y, hy⟩ ⟨y', hy'⟩)
  have hW'comm : ∀ a ∈ W', ∀ b ∈ W', a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, y, hy, rfl⟩ := hW'fac a ha
    obtain ⟨x', hx', y', hy', rfl⟩ := hW'fac b hb
    rw [hW'CN] at hx hx'
    have hyx' : y * x' = x' * y :=
      (Subgroup.mem_centralizer_iff.1 (hW'C (hW₂W' hy)) x' hx').symm
    have hy'x : y' * x = x * y' :=
      (Subgroup.mem_centralizer_iff.1 (hW'C (hW₂W' hy')) x hx).symm
    have hxx' : x * x' = x' * x :=
      congrArg Subtype.val (hE'el.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
    have hyy' := hW₂comm y hy y' hy'
    calc x * y * (x' * y') = x * (y * x') * y' := by group
      _ = x * (x' * y) * y' := by rw [hyx']
      _ = (x * x') * (y * y') := by group
      _ = (x' * x) * (y' * y) := by rw [hxx', hyy']
      _ = x' * (x * y') * y := by group
      _ = x' * (y' * x) * y := by rw [hy'x]
      _ = x' * y' * (x * y) := by group
  intro a ha b hb
  have ha' : g * a * g⁻¹ ∈ W' := by
    rw [← hUW']
    exact ⟨a, ha, rfl⟩
  have hb' : g * b * g⁻¹ ∈ W' := by
    rw [← hUW']
    exact ⟨b, hb, rfl⟩
  have hab := hW'comm _ ha' _ hb'
  calc a * b = g⁻¹ * ((g * a * g⁻¹) * (g * b * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * b * g⁻¹) * (g * a * g⁻¹)) * g := by rw [hab]
    _ = b * a := by group

end Ctx

theorem center3_of_noncyclic27
    (hX : D1NoXBlock3 G) {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {T : Subgroup G}
    (c : D2L34R27 G d P M A H R Rbar K T) (S : Sylow 3 ↥(ffC M T))
    (hS : ¬ IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype)) :
    Center3Conclusion M := by
  have ctx := c.ctx
  haveI := ctx.amb
  have hc := ctx.conf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT := c.sylow
  have hF : CharTwo M := (D2Amb3.glob (G := G)).charTwo M hc.esc.maxTwoLocal_M.1
  have hT1 : T ≠ ⊥ := by
    intro h
    apply twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_M.1
    rw [eq_bot_iff, ← h]
    exact CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT
  set Z := quasithinOmegaOneCenter T with hZdef
  set V := CFSG.Quasithin.conjClosure Z M with hVdef
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := CFSG.Quasithin.le_normalizer_conjClosure Z M
  have hZ1 : Z ≠ ⊥ := Setup.omegaOneCenterOf_ne_bot hT.2.1 hT1
  have hZ2 : IsPGroup 2 Z := hT.2.1.to_le (Setup.omegaOneCenterOf_le T)
  have hZT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (Z : Set G) :=
    CFSG.AGLEmbeddingD2.Tits.MsidePrelim.normalizer_le_normalizer_quasithinOmegaOneCenter T
  have hZloc : IsTwoLocal (Subgroup.normalizer (Z : Set G)) := ⟨Z, hZ1, hZ2, rfl⟩
  have hZM : ¬ Subgroup.normalizer (Z : Set G) ≤ M := fun h => c.not_normalizer_le (hZT.trans h)
  obtain ⟨hU, -⟩ := B2_15 hF hT
  have hCM : ffC M T ≤ M := inf_le_right
  have hCn : ((ffC M T).subgroupOf M).Normal := centralizer_inf_subgroupOf_normal hU hMV
  have hCnM : M ≤ Subgroup.normalizer ((ffC M T : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCM).1 hCn
  have hCZ : ffC M T ≤ Subgroup.normalizer (Z : Set G) :=
    inf_le_left.trans ((Subgroup.centralizer_le (CFSG.Quasithin.le_conjClosure Z M)).trans
      (Subgroup.centralizer_le_normalizer _))
  set D := (S : Subgroup ↥(ffC M T)).map (ffC M T).subtype with hD
  have hDC : D ≤ ffC M T := Subgroup.map_subtype_le _
  have hDp : IsPGroup 3 D := S.isPGroup'.map _
  obtain ⟨W, hWM, hWp, hWidx, hDW⟩ := exists_sylow_le (hDC.trans hCM) hDp
  have hWCc : ¬ IsCyclic ↥(W ⊓ ffC M T) := fun hcyc =>
    hS (Subgroup.isCyclic_of_le (H' := W ⊓ ffC M T) (le_inf hDW hDC))
  obtain ⟨E, hEX, hEel, hE9, hEcore⟩ := ctx.hasGoodE9_inf_normal hCM hCn hWM hWp hWidx hWCc
  have hEW : E ≤ W := hEX.trans inf_le_left
  have hEC : E ≤ ffC M T := hEX.trans inf_le_right
  have hEM : E ≤ M := hEC.trans hCM
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  have hEc : ¬ IsCyclic E := not_isCyclic_of_isElemAbelian hEel (by rw [hE9]; norm_num)
  have hWCp : IsPGroup 3 ↥(W ⊓ ffC M T) := hWp.to_le inf_le_left
  have hWE : W ≤ Subgroup.normalizer (E : Set G) := by
    intro w hw
    have hwM := hWM hw
    have hmapX : E.map (MulAut.conj w).toMonoidHom ≤ W ⊓ ffC M T := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨W.mul_mem (W.mul_mem hw (hEW hx)) (W.inv_mem hw),
        (Subgroup.mem_normalizer_iff.1 (hCnM hwM) x).1 (hEC hx)⟩
    have heq := c.eq_of_good hZloc hZM (inf_le_right.trans hCZ) (inf_le_right.trans hCM) hWCp
      hEX hEel hE9 hEcore hmapX (elementary_abelian_map 3 hEel _)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj w).injective, hE9])
      (glbCore_one_map_conj_le hwM hEcore)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hmem : w * x * w⁻¹ ∈ E.map (MulAut.conj w).toMonoidHom := ⟨x, hx, rfl⟩
      rwa [heq] at hmem
    · intro hx
      rw [← heq] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hyx' : w * y * w⁻¹ = w * x * w⁻¹ := hyx
      rwa [← mul_left_cancel (mul_right_cancel hyx')]
  set U := W ⊓ Subgroup.centralizer (E : Set G) with hUdef
  have hUW : U ≤ W := inf_le_left
  have hUp : IsPGroup 3 U := hWp.to_le hUW
  have hUC : U ≤ Subgroup.centralizer (E : Set G) := inf_le_right
  have hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEU : E ≤ U :=
    le_inf hEW fun e he => Subgroup.mem_centralizer_iff.2 fun e' he' => hEab e' he' e he
  obtain ⟨F, hFW, hFel, hF27⟩ := ctx.exists_E27_le_sylow hWM hWp hWidx
  obtain ⟨F', hF'EF, -, hF'27, hF'comm⟩ :=
    exists_E27_centralizing_of_normalizes hEel hE9 hFel hF27 (hFW.trans hWE)
  have hF'U : F' ≤ U :=
    le_inf (hF'EF.trans (sup_le hEW hFW)) fun f hf =>
      Subgroup.mem_centralizer_iff.2 fun e he => hF'comm e he f hf
  have hU27 : 27 ≤ Nat.card U := hF'27 ▸ Subgroup.card_le_of_le hF'U
  obtain ⟨N, hNM, hTN, hFN, hUN, hUidx, hNoX⟩ :=
    c.exists_subgroup_N hX hEC hEel hE9 hEcore hWM hWp hWidx hWE
  have hsN : Group.IsSolvable ↥N := by
    have := c.solvable
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hNM)
  set VN := CFSG.Quasithin.conjClosure Z N with hVNdef
  have hNVN : N ≤ Subgroup.normalizer (VN : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure Z N
  have hVNV : VN ≤ V := CFSG.Quasithin.conjClosure_mono le_rfl hNM
  obtain ⟨hUVN, -⟩ := B2_15 hFN hTN
  set CN := Subgroup.centralizer (VN : Set G) ⊓ N with hCNdef
  have hCNN : CN ≤ N := inf_le_right
  have hCNn : (CN.subgroupOf N).Normal := centralizer_inf_subgroupOf_normal hUVN hNVN
  have hNCN : N ≤ Subgroup.normalizer (CN : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCNN).1 hCNn
  have hCNZ : CN ≤ Subgroup.normalizer (Z : Set G) :=
    inf_le_left.trans ((Subgroup.centralizer_le (CFSG.Quasithin.le_conjClosure Z N)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hECN : E ≤ CN :=
    le_inf (hEC.trans (inf_le_left.trans (Subgroup.centralizer_le hVNV))) (hEU.trans hUN)
  have hUCN : U ⊓ CN = E :=
    c.eq_of_le_centralizer hZloc hZM (inf_le_right.trans hCNZ) (inf_le_left.trans (hUW.trans hWM))
      (hUp.to_le inf_le_left) (le_inf hEU hECN) hEel hE9 hEcore (inf_le_left.trans hUC)
  obtain ⟨X₂, B, hX₂1, hX₂2, hX₂T, hBN, hBX, hfacN⟩ : ∃ X₂ B : Subgroup G, X₂ ≠ ⊥ ∧
      IsPGroup 2 X₂ ∧ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₂ : Set G) ∧
      B ≤ N ∧ B ≤ Subgroup.normalizer (X₂ : Set G) ∧ ∀ n ∈ N, ∃ c ∈ CN, ∃ b ∈ B, n = c * b := by
    by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (VN : Set G)
    ·
      obtain ⟨-, hfac⟩ := CFSG.Quasithin.B2_7_of_le_factor hNVN hTN hJ
      refine ⟨thompsonJ T, N ⊓ Subgroup.normalizer (thompsonJ T : Set G),
        Setup.thompsonJ_ne_bot hT.2.1 hT1, hT.2.1.to_le (B6.thompsonJ_le T),
        GammaExtra.normalizer_le_normalizer_thompsonJ T, inf_le_left, inf_le_right, ?_⟩
      intro n hn
      obtain ⟨b, hb, c', hc', he⟩ := hfac n⁻¹ (N.inv_mem hn)
      refine ⟨c'⁻¹, ?_, b⁻¹, (N ⊓ Subgroup.normalizer (thompsonJ T : Set G)).inv_mem hb, ?_⟩
      · have := (N ⊓ Subgroup.centralizer (VN : Set G)).inv_mem hc'
        rw [inf_comm] at this
        exact this
      · rw [← mul_inv_rev, ← he, inv_inv]
    ·
      obtain ⟨hU', I, C₁, C₂, hNV', hI, hcard, hSylB, hJN, hdat⟩ :=
        exists_ffPairData_of_subgroup hFN hTN hsN hT1 hJ hNoX
      have hdat' := hdat
      obtain ⟨hC₁1, hC₁2, hC₂1, hC₂2, hT₁, hT₂, -, -, -⟩ := hdat'
      have hC₁loc : IsTwoLocal (Subgroup.normalizer (C₁ : Set G)) := ⟨C₁, hC₁1, hC₁2, rfl⟩
      have hC₁M : ¬ Subgroup.normalizer (C₁ : Set G) ≤ M := fun h =>
        c.not_normalizer_le (hT₁.trans h)
      obtain ⟨B, hBN, hBC₂, hfac⟩ := exists_factorization_of_pairData_of_bound hTN hNV' hI
        hcard hSylB hJN hdat (D := E) hECN hEp hEc fun Q hQ hQp hEQ => by
          have hQC := le_centralizer_of_sylow hUN hUp hUidx hUC hNCN hECN hUCN
            (hQ.trans inf_le_left) hQp hEQ
          have hQE := c.eq_of_le_centralizer hC₁loc hC₁M (hQ.trans inf_le_right)
            (hQ.trans (inf_le_left.trans hNM)) hQp hEQ hEel hE9 hEcore hQC
          rw [hQE, hE9]
      exact ⟨C₂, B, hC₂1, hC₂2, hT₂, hBN, hBC₂, hfac⟩
  have hUab : ∀ a ∈ W ⊓ Subgroup.centralizer (E : Set G),
      ∀ b ∈ W ⊓ Subgroup.centralizer (E : Set G), a * b = b * a :=
    c.comm_of_factorization hZ1 hZ2 hZT hX₂1 hX₂2 hX₂T hNM hUN hUp hUidx hU27 hEU hUC hEel hE9
      hEcore hCNN hNCN hCNZ hECN hUCN hBN hBX hfacN
  have hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M :=
    CFSG.ABGLocalTools.isPConstrained_of_isSolvable c.solvable
  obtain ⟨L, -, hLn, hEL, hLsmall⟩ := c.exists_normal_le_of_good hEC hEel hE9 hEcore
  obtain ⟨s, hsM, hsE, hs2⟩ :=
    c.exists_inverting_square hZ1 hZ2 hZT hEM (hEC.trans hCZ) hEel hE9 hEcore
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal ctx.setting ctx.sigma ctx.core
  have hPidx : ¬ 3 ∣ ((P : Subgroup G).subgroupOf M).index := fun h =>
    P.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hPM))
  have hmax : ∀ A' : Subgroup G, A' ≤ W → IsElemAbelian 3 A' → Nat.card A' ≤ 27 :=
    fun A' hA'W hA' =>
      card_le_of_isElemAbelian_of_pRank hPM P.isPGroup' hPidx hP3 (hA'W.trans hWM) hA'
  obtain ⟨P₀, hP₀W, hP₀3, hP₀n⟩ := exists_normal_order_three_le_of_tail3 hcon hLn hLsmall hWM
    hWp hWidx hEW hEL hE9 hEab hEel.2 hUab
    ⟨F, hFW, fun a ha b hb => congrArg Subtype.val (hFel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩),
      hFel.2, hF27⟩
    (fun A' hA' hab h3' => hmax A' hA' ⟨⟨⟨fun a b => Subtype.ext (hab a.1 a.2 b.1 b.2)⟩⟩, h3'⟩)
    hsM hsE hs2
  have hPO : P₀ ⊔ GLBPrimeCore 3 M ≤ M := sup_le (hP₀W.trans hWM) (glbPrimeCore_le 3 M)
  have hnormM : M ≤ Subgroup.normalizer ((GLBPrimeCore 3 M ⊔ P₀ : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hPO).1 hP₀n
  obtain ⟨E₀, hE₀W, hE₀el, hE₀9, hE₀C⟩ := exists_center3_of_normal_order_three hWM hWp
    (glbPrimeCore_coprime 3 M) (le_normalizer_glbPrimeCore 3 M) hEW hWE hEel hE9 hP₀W hP₀3
    hnormM hsM hsE hs2
  exact Center3Conclusion.of_central hWM hWp hWidx hE₀W hE₀el hE₀9 hE₀C

end CFSG.LocalAnalysis.RankThreeTheoremC
