module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Diag
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma33Proof
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop122

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S12

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G}

theorem nbr_neighbor_clause (h : Cfg12 G m p B x L D K) {y : G} (hy : y ∈ D) (hyx : y ∉ Subgroup.zpowers x)
    {M : Subgroup G} (hMK : M ≤ Ky p K y) (hnc : ¬ CentMod p M x) : GLANeighbor p x y M D K := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h.D_eq_sup hy hyx, Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  · rw [Ky, closureIn_eq_iSup_gLBConj] at hMK
    exact hMK
  · intro hle
    apply hnc
    have hOM : GLAPPrimeCoreOf p M ≤ M := Subgroup.map_subtype_le _
    have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (M : Set G) :=
      Subgroup.le_normalizer_iff_commutator_le_left.2 (hle.trans hOM)
    exact ⟨hxN (Subgroup.mem_zpowers x), hle⟩

theorem ky_comm_of_centMod (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) {y : G} (hy : y ∈ D)
    (hyx : y ∉ Subgroup.zpowers x) {M : Subgroup G}
    (hM : GLAPComponent p (Subgroup.centralizer ({y} : Set G)) M) (hMK : M ≤ Ky p K y) {b : G} (hb : b ∈ B)
    (hbM : CentMod p M b) :
    (⁅Ky p K y, Subgroup.zpowers b⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p (Ky p K y) := by
  have hp := h.prime
  obtain ⟨𝒞, hC1, hC2, hC3, hC4⟩ := ky_family h hin hy hyx
  have hM𝒞 : M ∈ 𝒞 := pcomp_mem_family hp hM hC1 (by rw [hC2]; exact hMK)
  have hle𝒞 : ∀ M' ∈ 𝒞, M' ≤ Ky p K y := fun M' hM' => by
    rw [← hC2]
    exact le_biSup (fun M'' => M'') hM'
  have key : ∀ M' ∈ 𝒞, (⁅M', Subgroup.zpowers b⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p (Ky p K y) := by
    intro M' hM'
    obtain ⟨e, he, rfl⟩ := hC4 M hM𝒞 M' hM'
    have hbx : b ∈ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute h.tri.bmax.1 hb h.tri.mem)
    have hez : e ∈ Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G) := by
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [S3.centralizer_zpowers b, Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
      exact (Commute.zpow_left (show Commute x b from (Subgroup.mem_centralizer_singleton_iff.1 hbx).symm) j).eq
    have h1 := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma33Ns.commutator_gLBConj_le (p := p) hez hbM.2
    have hKy : GLAPComponent p (Ky p K y) (GLBConj e M) :=
      glaPComponent_of_le hp (hC1 _ hM') (hle𝒞 _ hM') (ky_le_cy h hy)
    exact h1.trans (glaPPrimeCoreOf_le_of_isSubnormal hp hKy.2.1)
  have := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma33Ns.commutator_iSup_le (p := p) (X := Ky p K y)
    (S := Subgroup.zpowers b) hle𝒞 key
  rwa [hC2] at this

theorem mem_zpowers_y (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) {y : G} (hy : y ∈ D)
    (hyx : y ∉ Subgroup.zpowers x) {M : Subgroup G}
    (hM : GLAPComponent p (Subgroup.centralizer ({y} : Set G)) M) (hMK : M ≤ Ky p K y) (hnc : ¬ CentMod p M x)
    {b : G} (hb : b ∈ B) (hbM : CentMod p M b) : b ∈ Subgroup.zpowers y := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hKKy : K ≤ Ky p K y := le_closureIn_self K _
  have hcomm := ky_comm_of_centMod h hin hy hyx hM hMK hb hbM
  have hbK : b ∈ centModSubgroup p K := by
    refine ⟨B_norm_K h hb, fun k hk => ?_⟩
    have h1 : ⁅k, b⁆ ∈ GLAPPrimeCoreOf p (Ky p K y) :=
      hcomm (Subgroup.commutator_mem_commutator (hKKy hk) (Subgroup.mem_zpowers b))
    have h2 : ⁅k, b⁆ ∈ K := by
      have e : ⁅k, b⁆ = k * (b * k⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact K.mul_mem hk ((Subgroup.mem_normalizer_iff.1 (B_norm_K h hb) k⁻¹).1 (K.inv_mem hk))
    exact inf_primeCore_le hp hKKy ⟨h2, h1⟩
  have hbD : b ∈ D := by
    rw [← centMod_inf_eq h hin]
    exact ⟨hb, hbK⟩
  have hxz : Subgroup.zpowers x ≤ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
    refine fun u hu => Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    have hxy : Commute x y := (isElemAbelian_commute h.elem h.xD hy)
    exact (Commute.zpow_zpow hxy i j).eq.symm
  have hbD' : b ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) := by
    rw [← h.D_eq_sup hy hyx]
    exact hbD
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hxz] at hbD'
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hbD'
  have hvc : v ∈ Subgroup.centralizer (M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    have hmy : Commute w y := Subgroup.mem_centralizer_singleton_iff.1 (hM.1 hw)
    exact (hmy.zpow_right n).eq
  have hvM : v ∈ centModSubgroup p M := centMod_iff.1 (centMod_of_mem_centralizer hvc)
  have hbMs : u * v ∈ centModSubgroup p M := centMod_iff.1 hbM
  have huM : u ∈ centModSubgroup p M := by
    have := mul_mem hbMs (inv_mem hvM)
    simpa using this
  by_cases hu1 : u = 1
  · rw [hu1, one_mul]
    exact hv
  · exfalso
    have hord : orderOf x = p := orderOf_eq_prime (h.elem.2 x h.xD) h.tri.ne_one
    have hxu : x ∈ Subgroup.zpowers u := mem_zpowers_of_prime_order hord hu hu1
    exact hnc (centMod_iff.2 ((Subgroup.zpowers_le.2 huM) hxu))

theorem nbr_of_not_centMod (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) {y : G} (hy : y ∈ D)
    (hyx : y ∉ Subgroup.zpowers x) {M : Subgroup G}
    (hM : GLAPComponent p (Subgroup.centralizer ({y} : Set G)) M) (hMK : M ≤ Ky p K y) (hnc : ¬ CentMod p M x) :
    GLASHat p B y M ∧ GLANeighbor p x y M D K := by
  refine ⟨⟨h.tri.bmax, h.DB hy, fun h1 => hyx (h1 ▸ Subgroup.one_mem _), hM.1, hM, fun b => ⟨?_, ?_⟩⟩,
    nbr_neighbor_clause h hy hyx hMK hnc⟩
  · rintro ⟨hbB, hbN, hbc⟩
    exact mem_zpowers_y h hin hy hyx hM hMK hnc hbB ⟨hbN, hbc⟩
  · intro hb
    have hbB : b ∈ B := (Subgroup.zpowers_le.2 (h.DB hy)) hb
    have hbc : b ∈ Subgroup.centralizer (M : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      have hmy : Commute m y := Subgroup.mem_centralizer_singleton_iff.1 (hM.1 hm)
      exact hmy.zpow_right n
    have hcm := centMod_of_mem_centralizer (p := p) hbc
    exact ⟨hbB, hcm.1, hcm.2⟩

theorem noNbr_centMod (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) (hnn : NoNbr12 p B x L D K) {y : G}
    (hy : y ∈ D) (hyx : y ∉ Subgroup.zpowers x) {M : Subgroup G}
    (hM : GLAPComponent p (Subgroup.centralizer ({y} : Set G)) M) (hMK : M ≤ Ky p K y) : CentMod p M x := by
  by_contra hnc
  exact hnn y M (nbr_of_not_centMod h hin hy hyx hM hMK hnc)

theorem ky_single_of_centMod (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) {y : G} (hy : y ∈ D)
    (hyx : y ∉ Subgroup.zpowers x) {M : Subgroup G}
    (hM : GLAPComponent p (Subgroup.centralizer ({y} : Set G)) M) (hMK : M ≤ Ky p K y)
    (hxM : x ∈ Subgroup.normalizer (M : Set G)) : Ky p K y = M := by
  obtain ⟨𝒞, hC1, hC2, hC3, hC4⟩ := ky_family h hin hy hyx
  have hM𝒞 : M ∈ 𝒞 := pcomp_mem_family h.prime hM hC1 (by rw [hC2]; exact hMK)
  apply le_antisymm
  · rw [← hC2]
    refine iSup₂_le fun M' hM' => ?_
    obtain ⟨e, he, rfl⟩ := hC4 M hM𝒞 M' hM'
    have heN : e ∈ Subgroup.normalizer (M : Set G) := (Subgroup.zpowers_le.2 hxM) he
    rw [mem_normalizer_iff_gLBConj_eq.1 heN]
  · exact hMK

theorem Ky_single (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) (hnn : NoNbr12 p B x L D K) {y : G}
    (hy : y ∈ D) (hyx : y ∉ Subgroup.zpowers x) :
    ∃ M : Subgroup G, GLAPComponent p (Subgroup.centralizer ({y} : Set G)) M ∧ Ky p K y = M ∧ CentMod p M x := by
  obtain ⟨𝒞, hC1, hC2, hC3, hC4⟩ := ky_family h hin hy hyx
  have hne : 𝒞.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hKy : K ≤ Ky p K y := le_closureIn_self K _
    rw [← hC2, hemp] at hKy
    simp at hKy
    haveI := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_nontrivial h.K_qs
    exact (Subgroup.nontrivial_iff_ne_bot K).1 this hKy
  obtain ⟨M, hM𝒞⟩ := hne
  have hMK : M ≤ Ky p K y := by
    rw [← hC2]
    exact le_biSup (fun M' => M') hM𝒞
  have hc := noNbr_centMod h hin hnn hy hyx (hC1 M hM𝒞) hMK
  exact ⟨M, hC1 M hM𝒞, ky_single_of_centMod h hin hy hyx (hC1 M hM𝒞) hMK hc.1, hc⟩

theorem cover_of_centMod (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) {y : G} (hy : y ∈ D)
    (hyx : y ∉ Subgroup.zpowers x) {M : Subgroup G}
    (hM : GLAPComponent p (Subgroup.centralizer ({y} : Set G)) M) (hMy : Ky p K y = M) (hc : CentMod p M x) :
    M = K ⊔ GLAPPrimeCoreOf p M := by
  have hKc := ky_pcomp_cent h hin hy hyx
  rw [hMy] at hKc
  obtain ⟨-, hall, -, -, hsup, -⟩ :=
    glaPLayer_inf_centralizer h.prime hM (isPGroup_zpowers_of_mem h.elem h.xD) hc
  rw [← hall K hKc] at hsup
  exact hsup.symm

theorem mem_normalizer_biSup {S : Set (Subgroup G)} {n : G}
    (h : ∀ M' ∈ S, n ∈ Subgroup.normalizer (M' : Set G)) :
    n ∈ Subgroup.normalizer ((⨆ M' ∈ S, M' : Subgroup G) : Set G) := by
  have hle : ∀ n : G, (∀ M' ∈ S, n ∈ Subgroup.normalizer (M' : Set G)) →
      GLBConj n (⨆ M' ∈ S, M') ≤ ⨆ M' ∈ S, M' := by
    intro n hn
    refine (Subgroup.map_le_iff_le_comap).2 (iSup₂_le fun M' hM' => ?_)
    rw [← Subgroup.map_le_iff_le_comap]
    show GLBConj n M' ≤ _
    rw [gLBConj_eq_of_mem_normalizer (hn M' hM')]
    exact le_biSup (fun M'' => M'') hM'
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (hle n h) ?_
  have h' := gLBConj_mono (g := n) (hle n⁻¹ fun M' hM' => Subgroup.inv_mem _ (h M' hM'))
  rwa [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h'

theorem layer_normalizes_closure {p : ℕ} (hp : p.Prime) {Y M : Subgroup G} {x : G} (hM : GLAPComponent p Y M)
    (hxY : x ∈ Y) : GLAPLayer p Y ≤ Subgroup.normalizer (closureIn M (Subgroup.zpowers x) : Set G) := by
  rw [closureIn_zpowers_eq_iSup]
  refine sSup_le fun N hN n hn => ?_
  by_cases hNS : N ∈ conjFam x M
  · exact Subgroup.le_normalizer (le_biSup (fun M' => M') hNS hn)
  · refine mem_normalizer_biSup fun M' hM' => ?_
    exact CFSG.HardMathSupport.Solomon.LocalBalance.mem_normalizer_of_ne hp (conjFam_comp hM hxY M' hM') hN
      (fun heq => hNS (heq ▸ hM')) hn

theorem diag_pcomp_le_K (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) {y : G} (hy : y ∈ D)
    (hyx : y ∉ Subgroup.zpowers x) {M P : Subgroup G}
    (hM : GLAPComponent p (Subgroup.centralizer ({y} : Set G)) M)
    (hP : GLAPComponent p (closureIn M (Subgroup.zpowers x) ⊓ Subgroup.centralizer ({x} : Set G)) P) : P ≤ K := by
  have hp := h.prime
  have hxy : x ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact isElemAbelian_commute h.elem h.xD hy
  have hS := conjFam_comp hM hxy
  have hJL : closureIn M (Subgroup.zpowers x) ≤ GLAPLayer p (Subgroup.centralizer ({y} : Set G)) := by
    rw [closureIn_zpowers_eq_iSup]
    exact iSup₂_le fun M' hM' => le_sSup (hS M' hM')
  have hnorm := layer_normalizes_closure hp hM hxy
  have hsub : IsSubnormal (closureIn M (Subgroup.zpowers x) ⊓ Subgroup.centralizer ({x} : Set G))
      (GLAPLayer p (Subgroup.centralizer ({y} : Set G)) ⊓ Subgroup.centralizer ({x} : Set G)) :=
    IsSubnormal.step (inf_le_inf_right _ hJL)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_inf_right _ hJL)).2
        fun g hg => mem_normalizer_inf' (hnorm hg.1) (Subgroup.le_normalizer hg.2))
      (IsSubnormal.refl _)
  have hPc := glaPComponent_of_isSubnormal' hp hsub hP
  have hPle : P ≤ GLAPLayer p (GLAPLayer p (Subgroup.centralizer ({y} : Set G)) ⊓ Subgroup.centralizer ({x} : Set G)) :=
    le_sSup hPc
  have hxp : IsPGroup p (Subgroup.zpowers x) := isPGroup_zpowers_of_mem h.elem h.xD
  have hyp : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_of_mem h.elem hy
  have hcomm : ∀ d ∈ Subgroup.zpowers y, ∀ e ∈ Subgroup.zpowers x, d * e = e * d := fun d hd e he => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    exact (Commute.zpow_zpow (isElemAbelian_commute h.elem hy h.xD) i j).eq
  have hbal := hin.bal hp h.ctx.ctx.ctx.kProper (Subgroup.zpowers y) (Subgroup.zpowers x) hyp hxp hcomm
  rw [S3.centralizer_zpowers y, S3.centralizer_zpowers x] at hbal
  rw [hbal, inf_comm, ← h.cs_eq hy hyx, std_layer h hin] at hPle
  exact hPle

theorem diag_not_in_Ky (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) {y : G} (hy : y ∈ D)
    (hyx : y ∉ Subgroup.zpowers x) {M P : Subgroup G}
    (hM : GLAPComponent p (Subgroup.centralizer ({y} : Set G)) M) (hMK : ¬ M ≤ Ky p K y)
    (hP : GLAPComponent p (closureIn M (Subgroup.zpowers x) ⊓ Subgroup.centralizer ({x} : Set G)) P) :
    ¬ P ≤ Ky p K y := by
  intro hPK
  have hp := h.prime
  have hxy : x ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact isElemAbelian_commute h.elem h.xD hy
  have hS := conjFam_comp hM hxy
  obtain ⟨𝒞, hC1, hC2, -, -⟩ := ky_family h hin hy hyx
  have hxKy : x ∈ Subgroup.normalizer (Ky p K y : Set G) := ky_norm h hy h.tri.mem
  have hKyc : Ky p K y ≤ Subgroup.centralizer ({y} : Set G) := ky_le_cy h hy
  have hMi : ∀ M' ∈ conjFam x M, ¬ M' ≤ Ky p K y := by
    rintro _ ⟨e, he, rfl⟩ hle
    apply hMK
    have heN : e⁻¹ ∈ Subgroup.normalizer (Ky p K y : Set G) :=
      Subgroup.inv_mem _ ((Subgroup.zpowers_le.2 hxKy) he)
    have h1 := gLBConj_mono (g := e⁻¹) hle
    rwa [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one, gLBConj_eq_of_mem_normalizer heN] at h1
  have hcomm1 : ∀ M' ∈ conjFam x M, ⁅M', Ky p K y⁆ ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({y} : Set G)) := by
    intro M' hM'
    rw [Subgroup.commutator_comm, ← hC2]
    refine CFSG.HardMathSupport.Solomon.LocalBalance.Lemma33Ns.commutator_iSup_le (p := p) (𝒞 := 𝒞)
      (fun K' hK' => (hC1 K' hK').1) fun K' hK' => ?_
    rw [Subgroup.commutator_comm]
    refine CFSG.HardMathSupport.Solomon.LocalBalance.commutator_le_gLAPPrimeCore_of_ne hp (hS M' hM') (hC1 K' hK')
      fun heq => hMi M' hM' ?_
    rw [heq, ← hC2]
    exact le_biSup (fun M'' => M'') hK'
  have hcomm : ⁅closureIn M (Subgroup.zpowers x), Ky p K y⁆ ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({y} : Set G)) := by
    rw [closureIn_zpowers_eq_iSup]
    exact CFSG.HardMathSupport.Solomon.LocalBalance.Lemma33Ns.commutator_iSup_le (p := p) (S := Ky p K y)
      (fun M' hM' => (hS M' hM').1) hcomm1
  have hPJ : P ≤ closureIn M (Subgroup.zpowers x) := hP.1.trans inf_le_left
  have hPO : P ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({y} : Set G)) := by
    have h1 : (⁅P, P⁆ : Subgroup G) = P := glaPComponent_perfect hP
    rw [← h1]
    exact (Subgroup.commutator_mono hPJ hPK).trans hcomm
  have hJL : closureIn M (Subgroup.zpowers x) ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [closureIn_zpowers_eq_iSup]
    exact iSup₂_le fun M' hM' => (hS M' hM').1
  have hPO' : P ≤ GLAPPrimeCoreOf p P := fun z hz => inf_primeCore_le hp (hPJ.trans hJL) ⟨hz, hPO hz⟩
  apply glaPPrimeCore_ne_top_of_glaPComponent hP
  rw [eq_top_iff]
  intro u _
  obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 (hPO' u.2)
  have : v = u := Subtype.ext hvu
  exact this ▸ hv

theorem x_norm_comps (h : Cfg12 G m p B x L D K) (hin : CommonInputs G p) (hnn : NoNbr12 p B x L D K) {y : G}
    (hy : y ∈ D) (hyx : y ∉ Subgroup.zpowers x) {M : Subgroup G}
    (hM : GLAPComponent p (Subgroup.centralizer ({y} : Set G)) M) : x ∈ Subgroup.normalizer (M : Set G) := by
  by_cases hMK : M ≤ Ky p K y
  · exact (noNbr_centMod h hin hnn hy hyx hM hMK).1
  · by_contra hxM
    have hxy : x ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact isElemAbelian_commute h.elem h.xD hy
    obtain ⟨P, hP⟩ := diag_pcomp_exists (x := x) h.prime hM hxy (h.elem.2 x h.xD) hxM
    exact diag_not_in_Ky h hin hy hyx hM hMK hP ((diag_pcomp_le_K h hin hy hyx hM hP).trans (le_closureIn_self K _))

end S12

end CFSG.LocalAnalysis.GLTheoremA
