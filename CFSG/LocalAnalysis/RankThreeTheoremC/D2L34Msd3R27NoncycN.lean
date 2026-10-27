module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Escape
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Good
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.ThompsonFactor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.TwoOfThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3NoncycSquare
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WNoncycA

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim

variable {G : Type} [Group G] [Finite G]
variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {T : Subgroup G}

private theorem relIndex_sup_left_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) : A.relIndex (A ⊔ B) = A.relIndex B := by
  have hBS : B ≤ B ⊔ A := le_sup_left
  have : (A.subgroupOf (B ⊔ A)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hB
  have hsup : B.subgroupOf (B ⊔ A) ⊔ A.subgroupOf (B ⊔ A) = ⊤ :=
    codisjoint_iff.1 (Subgroup.codisjoint_subgroupOf_sup B A)
  have h1 := Subgroup.relIndex_sup_right (B.subgroupOf (B ⊔ A)) (A.subgroupOf (B ⊔ A))
  rw [hsup, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hBS] at h1
  rw [sup_comm]
  exact h1

private theorem relIndex_sup_right_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  have h0 := relIndex_sup_left_of_le_normalizer hB
  have h1 := Subgroup.relIndex_mul_card B (A ⊔ B)
  have h2 := Subgroup.relIndex_mul_card B A
  have h3 := Subgroup.relIndex_mul_card A (A ⊔ B)
  have h4 := Subgroup.relIndex_mul_card A B
  rw [inf_eq_left.mpr le_sup_right] at h1
  rw [inf_eq_left.mpr le_sup_left, h0] at h3
  rw [inf_comm] at h2
  have hpos : 0 < A.relIndex B * Nat.card ↥(A ⊓ B) := by
    rw [h4]
    exact Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc B.relIndex (A ⊔ B) * (A.relIndex B * Nat.card ↥(A ⊓ B))
      = B.relIndex (A ⊔ B) * Nat.card B := by rw [h4]
    _ = Nat.card ↥(A ⊔ B) := h1
    _ = A.relIndex B * Nat.card A := h3.symm
    _ = A.relIndex B * (B.relIndex A * Nat.card ↥(A ⊓ B)) := by rw [h2]
    _ = B.relIndex A * (A.relIndex B * Nat.card ↥(A ⊓ B)) := by ring

omit [Finite G] in
private theorem exists_mul_pow_eq {K S : Subgroup G}
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) {k s : G} (hk : k ∈ K) (hs : s ∈ S) :
    ∀ m : ℕ, ∃ k' ∈ K, (k * s) ^ m = k' * s ^ m
  | 0 => ⟨1, K.one_mem, by simp⟩
  | m + 1 => by
    obtain ⟨k', hk', h⟩ := exists_mul_pow_eq hSK hk hs m
    refine ⟨k' * (s ^ m * k * (s ^ m)⁻¹), K.mul_mem hk'
      ((Subgroup.mem_normalizer_iff.mp (hSK (S.pow_mem hs m)) k).mp hk), ?_⟩
    rw [pow_succ, h, pow_succ]
    group

omit [Finite G] in
private theorem exists_pow_two_pow_mem {N₁ T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (N₁ : Set G)) (hT2 : IsPGroup 2 T) {x : G}
    (hx : x ∈ N₁ ⊔ T) : ∃ k : ℕ, x ^ 2 ^ k ∈ N₁ := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N₁ T hT] at hx
  obtain ⟨n, hn, t, ht, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨n', hn', h⟩ := exists_mul_pow_eq hT hn ht (2 ^ k)
  refine ⟨k, ?_⟩
  rw [h, hk', mul_one]
  exact hn'

omit [Finite G] in
private theorem isSubnormal_trans' {A B C : Subgroup G} (hAB : IsSubnormal A B)
    (hBC : IsSubnormal B C) : IsSubnormal A C := by
  revert hBC
  induction hAB with
  | refl => exact id
  | step hHM hn _ ih => exact fun hBC => IsSubnormal.step hHM hn (ih hBC)

omit [Finite G] in
private theorem isSubnormal_inf_of_le {A B K : Subgroup G} (hAB : IsSubnormal A B)
    (hKB : K ≤ B) : IsSubnormal (A ⊓ K) K := by
  revert hKB
  induction hAB with
  | refl H =>
    intro hKH
    rw [inf_eq_right.mpr hKH]
    exact IsSubnormal.refl K
  | step hHM hn _ ih =>
    intro hKB
    refine IsSubnormal.step (inf_le_inf_right K hHM) ⟨fun x hx y => ?_⟩ (ih hKB)
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have h := hn.conj_mem ⟨x, (x.2).1⟩ (Subgroup.mem_subgroupOf.mpr hx.1) ⟨y, (y.2).1⟩
    rw [Subgroup.mem_subgroupOf] at h
    exact ⟨h, K.mul_mem (K.mul_mem (y.2).2 hx.2) (K.inv_mem (y.2).2)⟩

theorem D2L34R27.exists_normal_le_of_good
    (c : D2L34R27 G d P M A H R Rbar K T) {E : Subgroup G} (hEC : E ≤ ffC M T)
    (hEel : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hEcore : GLBCore 3 1 E ≤ M) :
    ∃ L : Subgroup G, L ≤ M ∧ (L.subgroupOf M).Normal ∧ E ≤ L ∧
      ∀ Q : Subgroup G, Q ≤ L → IsPGroup 3 Q → Nat.card Q ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := c.amb
  have hc := c.ctx.conf
  have hT := c.sylow
  set Z := quasithinOmegaOneCenter T
  set V := CFSG.Quasithin.conjClosure Z M
  have hMN : M ≤ Subgroup.normalizer (V : Set G) := CFSG.Quasithin.le_normalizer_conjClosure Z M
  have hF : CharTwo M := (D2Amb3.glob (G := G)).charTwo M hc.esc.maxTwoLocal_M.1
  obtain ⟨hU, -⟩ := B2_15 hF hT
  have hCn : ((ffC M T).subgroupOf M).Normal := centralizer_inf_subgroupOf_normal hU hMN
  have hT1 : T ≠ ⊥ := by
    intro h
    apply twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_M.1
    rw [eq_bot_iff, ← h]
    exact CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hZ1 : Z ≠ ⊥ := Setup.omegaOneCenterOf_ne_bot hT.2.1 hT1
  have hZ2 : IsPGroup 2 Z := hT.2.1.to_le (Setup.omegaOneCenterOf_le T)
  have hTZ :=
    CFSG.AGLEmbeddingD2.Tits.MsidePrelim.normalizer_le_normalizer_quasithinOmegaOneCenter T
  have hNZ : ¬ Subgroup.normalizer (Z : Set G) ≤ M := fun h => c.not_normalizer_le (hTZ.trans h)
  have hCZ : ffC M T ≤ Subgroup.normalizer (Z : Set G) := by
    refine inf_le_left.trans ?_
    exact (Subgroup.centralizer_le (CFSG.Quasithin.le_conjClosure Z M)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCM : ffC M T ≤ M := inf_le_right
  have hEM : E ≤ M := hEC.trans hCM
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  obtain ⟨N₁, E₀, d₁, Rbar₁, K₁, hNN₁, -, -, hconf⟩ :=
    c.exists_conf_of_good (⟨Z, hZ1, hZ2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (Z : Set G)))
      hTZ hNZ (hEC.trans hCZ) hEM hEp le_rfl hEel hE9 hEcore
  have hEN₁ : E ≤ N₁ := (hEC.trans hCZ).trans hNN₁
  set F : Subgroup G := (((E.subgroupOf N₁).map
    (QuotientGroup.mk' (primeComplementCore (G := N₁) 3))).comap
      (QuotientGroup.mk' (primeComplementCore (G := N₁) 3))).map N₁.subtype
  have hconjF : ∀ m ∈ M, ∀ x ∈ E, m * x * m⁻¹ ∈ F := by
    intro m hm x hx
    have hEmC : E.map (MulAut.conj m).toMonoidHom ≤ ffC M T := by
      rintro _ ⟨e, he, rfl⟩
      have h := hCn.conj_mem ⟨e, hEM he⟩ (Subgroup.mem_subgroupOf.mpr (hEC he)) ⟨m, hm⟩
      rw [Subgroup.mem_subgroupOf] at h
      simpa [MulAut.conj_apply] using h
    have hEmN₁ : E.map (MulAut.conj m).toMonoidHom ≤ N₁ := hEmC.trans (hCZ.trans hNN₁)
    have hmap := hconf.map_eq_of_good (le_inf hEmN₁ (hEmC.trans hCM))
      (elementary_abelian_map 3 hEel _)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj m).injective, hE9])
      (glbCore_one_map_conj_le hm hEcore)
    have hxEm : m * x * m⁻¹ ∈ E.map (MulAut.conj m).toMonoidHom :=
      ⟨x, hx, by simp [MulAut.conj_apply]⟩
    refine ⟨⟨m * x * m⁻¹, hEmN₁ hxEm⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, ← hmap]
    exact ⟨⟨m * x * m⁻¹, hEmN₁ hxEm⟩, Subgroup.mem_subgroupOf.mpr hxEm, rfl⟩
  set L₀ : Subgroup M := Subgroup.normalClosure ((E.subgroupOf M : Subgroup M) : Set M)
  have hL₀ : (L₀.map M.subtype).subgroupOf M = L₀ :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hL₀F : L₀ ≤ F.comap M.subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
    exact hconjF g g.2 a (Subgroup.mem_subgroupOf.mp ha)
  refine ⟨L₀.map M.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [hL₀]
    exact Subgroup.normalClosure_normal
  · intro x hx
    exact ⟨⟨x, hEM hx⟩, Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  · intro Q hQL hQp
    have hQF : Q ≤ F := fun q hq => by
      obtain ⟨y, hy, rfl⟩ := hQL hq
      exact hL₀F hy
    have hQN₁ : Q ≤ N₁ := hQF.trans (Subgroup.map_subtype_le _)
    have hQp' : IsPGroup 3 (Q.subgroupOf N₁) :=
      hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQN₁).symm
    have hEp' : IsPGroup 3 (E.subgroupOf N₁) :=
      hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEN₁).symm
    have hle : (Q.subgroupOf N₁).map (QuotientGroup.mk' (primeComplementCore (G := N₁) 3)) ≤
        (E.subgroupOf N₁).map (QuotientGroup.mk' (primeComplementCore (G := N₁) 3)) := by
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨q', hq', hqq'⟩ := hQF (Subgroup.mem_subgroupOf.mp hq)
      have hqe : q' = q := Subtype.ext hqq'
      subst hqe
      exact hq'
    calc Nat.card Q = Nat.card (Q.subgroupOf N₁) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN₁).toEquiv).symm
      _ = Nat.card ((Q.subgroupOf N₁).map
            (QuotientGroup.mk' (primeComplementCore (G := N₁) 3))) :=
          (card_map_mk_of_isPGroup Nat.prime_three _ (primeComplementCore_coprime 3) hQp').symm
      _ ≤ Nat.card ((E.subgroupOf N₁).map
            (QuotientGroup.mk' (primeComplementCore (G := N₁) 3))) := Subgroup.card_le_of_le hle
      _ = Nat.card (E.subgroupOf N₁) :=
          card_map_mk_of_isPGroup Nat.prime_three _ (primeComplementCore_coprime 3) hEp'
      _ = 9 := by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN₁).toEquiv, hE9]

theorem D2L34R27.exists_subgroup_N
    (hX : D1NoXBlock3 G)
    (c : D2L34R27 G d P M A H R Rbar K T) {E W : Subgroup G} (hEC : E ≤ ffC M T)
    (hEel : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hEcore : GLBCore 3 1 E ≤ M)
    (hWM : W ≤ M) (hWp : IsPGroup 3 W) (hWidx : ¬ 3 ∣ (W.subgroupOf M).index)
    (hWE : W ≤ Subgroup.normalizer (E : Set G)) :
    ∃ N : Subgroup G, N ≤ M ∧ IsSylowTwoOf T N ∧ CharTwo N ∧
      W ⊓ Subgroup.centralizer (E : Set G) ≤ N ∧
      ¬ 3 ∣ ((W ⊓ Subgroup.centralizer (E : Set G)).subgroupOf N).index ∧
      ∀ Y : Subgroup G, Y ≤ N → IsSubnormal Y N → InClassXBlock Y → False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := c.amb
  have hc := c.ctx.conf
  have hT := c.sylow
  have hF : CharTwo M := (D2Amb3.glob (G := G)).charTwo M hc.esc.maxTwoLocal_M.1
  obtain ⟨L, hLM, hLn, hEL, hLb⟩ := c.exists_normal_le_of_good hEC hEel hE9 hEcore
  have hEM : E ≤ M := hEC.trans inf_le_right
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  have hEidx : ¬ 3 ∣ (E.subgroupOf L).index := by
    obtain ⟨S, hSL, hSp, hSidx, hES⟩ := exists_sylow_le hEL hEp
    have hSE : E = S := Subgroup.eq_of_le_of_card_ge hES (by rw [hE9]; exact hLb S hSL hSp)
    rw [hSE]
    exact hSidx
  have hML : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn
  have hfrat : ∀ m ∈ M, ∃ g ∈ L, ∀ e ∈ E, ∃ e' ∈ E, g * m * e' * (g * m)⁻¹ = e := by
    intro m hm
    have hEmL : E.map (MulAut.conj m).toMonoidHom ≤ L := by
      rintro _ ⟨e, he, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hML hm) e).mp (hEL he)
    obtain ⟨g, hgL, hgE⟩ := exists_conj_map_le_of_isPGroup hEL hEp hEidx hEmL (hEp.map _)
    have heq : (E.map (MulAut.conj m).toMonoidHom).map (MulAut.conj g).toMonoidHom = E :=
      Subgroup.eq_of_le_of_card_ge hgE (le_of_eq (by
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
          Subgroup.card_map_of_injective (MulAut.conj m).injective]))
    refine ⟨g, hgL, fun e he => ?_⟩
    rw [← heq] at he
    obtain ⟨_, ⟨e', he', rfl⟩, rfl⟩ := he
    refine ⟨e', he', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  set C : Subgroup G := M ⊓ Subgroup.centralizer (E : Set G) with hCdef
  set N₁ : Subgroup G := L ⊔ C with hN₁def
  have hCN₁ : C ≤ N₁ := le_sup_right
  have hLN₁ : L ≤ N₁ := le_sup_left
  have hN₁M : N₁ ≤ M := sup_le hLM inf_le_left
  have hconjN₁ : ∀ m ∈ M, ∀ x ∈ N₁, m * x * m⁻¹ ∈ N₁ := by
    intro m hm
    suffices h : N₁ ≤ N₁.comap (MulAut.conj m).toMonoidHom from fun x hx => h hx
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · show m * x * m⁻¹ ∈ N₁
      exact hLN₁ ((Subgroup.mem_normalizer_iff.mp (hML hm) x).mp hx)
    · show m * x * m⁻¹ ∈ N₁
      obtain ⟨g, hgL, hg⟩ := hfrat m hm
      have hgm : g * m ∈ M := M.mul_mem (hLM hgL) hm
      have hk : g * m * x * (g * m)⁻¹ ∈ C := by
        refine Subgroup.mem_inf.mpr ⟨M.mul_mem (M.mul_mem hgm hx.1) (M.inv_mem hgm), ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        obtain ⟨e', he', rfl⟩ := hg e he
        have hxe' : e' * x = x * e' := Subgroup.mem_centralizer_iff.mp hx.2 e' he'
        calc g * m * e' * (g * m)⁻¹ * (g * m * x * (g * m)⁻¹)
            = g * m * (e' * x) * (g * m)⁻¹ := by group
          _ = g * m * (x * e') * (g * m)⁻¹ := by rw [hxe']
          _ = g * m * x * (g * m)⁻¹ * (g * m * e' * (g * m)⁻¹) := by group
      have e : m * x * m⁻¹ = g⁻¹ * (g * m * x * (g * m)⁻¹) * g := by group
      rw [e]
      exact N₁.mul_mem (N₁.mul_mem (N₁.inv_mem (hLN₁ hgL)) (hCN₁ hk)) (hLN₁ hgL)
  have hN₁n : (N₁.subgroupOf M).Normal := ⟨fun x hx m => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hconjN₁ m m.2 x hx⟩
  have hTN₁ : T ≤ Subgroup.normalizer (N₁ : Set G) :=
    hT.1.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hN₁M).mp hN₁n)
  set N : Subgroup G := N₁ ⊔ T with hNdef
  have hN₁N : N₁ ≤ N := le_sup_left
  have hTN : T ≤ N := le_sup_right
  have hNM : N ≤ M := sup_le hN₁M hT.1
  have hQC : W ⊓ Subgroup.centralizer (E : Set G) ≤ C := fun x hx => ⟨hWM hx.1, hx.2⟩
  have hWC : W ≤ Subgroup.normalizer (C : Set G) := by
    have h1 : W ≤ Subgroup.normalizer (M : Set G) := hWM.trans Subgroup.le_normalizer
    have h2 : W ≤ Subgroup.normalizer
        ((Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) :=
      hWE.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer _)).mp
          (Subgroup.normal_subgroupOf_centralizer_normalizer _))
    exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hi1 : ¬ 3 ∣ (W ⊓ Subgroup.centralizer (E : Set G)).relIndex C := by
    have heq : W ⊓ Subgroup.centralizer (E : Set G) = W ⊓ C := by
      rw [hCdef, ← inf_assoc, inf_eq_left.mpr hWM]
    rw [heq, Subgroup.inf_relIndex_right, ← relIndex_sup_right_of_le_normalizer hWC]
    intro h
    exact hWidx (h.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex W (C ⊔ W) M
      le_sup_right (sup_le inf_le_left hWM))))
  have hEC' : E ≤ C := fun x hx =>
    ⟨hEM hx, Subgroup.le_centralizer_iff_isMulCommutative.mpr hEel.1 hx⟩
  have hi2 : ¬ 3 ∣ C.relIndex N₁ := by
    rw [hN₁def, relIndex_sup_right_of_le_normalizer (inf_le_left.trans hML)]
    intro h
    exact hEidx (h.trans (Subgroup.relIndex_dvd_of_le_left L hEC'))
  have hi3 : ¬ 3 ∣ N₁.relIndex N := by
    rw [hNdef, relIndex_sup_left_of_le_normalizer hTN₁]
    intro h
    obtain ⟨k, hk⟩ := hT.2.1.exists_card_eq
    have hdvd : N₁.relIndex T ∣ 2 ^ k := by
      rw [← hk]
      exact Dvd.intro _ (Subgroup.relIndex_mul_card N₁ T)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (h.trans hdvd)) (by norm_num)
  have hidx : ¬ 3 ∣ (W ⊓ Subgroup.centralizer (E : Set G)).relIndex N := by
    rw [← Subgroup.relIndex_mul_relIndex _ C N hQC (hCN₁.trans hN₁N),
      ← Subgroup.relIndex_mul_relIndex C N₁ N hCN₁ hN₁N]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · exact hi1 h
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · exact hi2 h
      · exact hi3 h
  refine ⟨N, hNM, ⟨hTN, hT.2.1, fun h => hT.2.2 (h.trans
    (Dvd.intro _ (Subgroup.relIndex_mul_relIndex T N M hTN hNM)))⟩,
    charTwo_of_le_of_pCoreOf_le hNM hF
      ((CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT).trans hTN),
    hQC.trans (hCN₁.trans hN₁N), hidx, ?_⟩
  intro Y hYN hYsn hYX
  have hYM : Y ≤ M := hYN.trans hNM
  have hYN₁ : Y ≤ N₁ := by
    haveI : (N₁.subgroupOf Y).Normal := ⟨fun x hx y => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hconjN₁ y (hYM y.2) x hx⟩
    have htop := hYX.1.1 (N₁.subgroupOf Y) (fun g => by
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
      obtain ⟨k, hk⟩ := exists_pow_two_pow_mem hTN₁ hT.2.1 (hYN y.2)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk)
    intro y hy
    have hmem : (⟨y, hy⟩ : Y) ∈ N₁.subgroupOf Y := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  have hYsn₁ : IsSubnormal Y N₁ := by
    have h := isSubnormal_inf_of_le hYsn hN₁N
    rwa [inf_eq_left.mpr hYN₁] at h
  exact noXBlockFor_of_setting hX c.ctx.setting M Y hc.esc.maxTwoLocal_M hYM
    (isSubnormal_trans' hYsn₁ (IsSubnormal.step hN₁M hN₁n (IsSubnormal.refl M))) hYX

end CFSG.LocalAnalysis.RankThreeTheoremC
