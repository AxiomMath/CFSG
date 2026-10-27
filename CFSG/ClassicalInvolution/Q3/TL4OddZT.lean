module

public import CFSG.ClassicalInvolution.Q3.TL4VtxTwin
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Model
public import CFSG.ClassicalInvolution.Q3.TL4E3TQSect
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetDefs
public import CFSG.ClassicalInvolution.Q3.TL4OddFrVtx
public import CFSG.ClassicalInvolution.Q3.TL4VtxLay
public import CFSG.ClassicalInvolution.Q3.TL4VtxAut

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open scoped commutatorElement

@[expose] def OmegaAutOddFreeR : Prop :=
  ∀ (M : Type) [Group M] [Finite M], PhilipHall.Frame.CentOmega3 M →
    Q3NM.AutOddFree (M ⧸ Subgroup.center M)

theorem isSimpleGroup_of_centOmega3 {M : Type} [Group M] (h : PhilipHall.Frame.CentOmega3 M) :
    IsSimpleGroup (M ⧸ Subgroup.center M) := by
  rcases h with hQ | hQ | hQ | ⟨k, hk, hQ⟩ | ⟨k, hk, hQ⟩ | ⟨k, hk, hQ⟩
  · rcases hQ with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 3 1 hcl
    all_goals omega
  · rcases hQ with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 4 3 1 hcl).2
    all_goals omega
  · rcases hQ with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 4 3 1 hcl).2
    all_goals omega
  · rcases hQ with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaOdd _ k
        3 1 hcl).2
    all_goals omega
  · rcases hQ with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus _ k
        3 1 hcl).2
    all_goals omega
  · rcases hQ with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaMinus _ k
        3 1 hcl).2
    all_goals omega

theorem autOddFree_of_centOmega3 (hOm : OmegaAutOddFreeR) {Q : Type} [Group Q] [Finite Q]
    {X L : Subgroup Q} (hLX : L ≤ X) (hLn : (L.subgroupOf X).Normal) (hL : IsComponent L)
    (h : PhilipHall.Frame.CentOmega3 (↥X ⧸ Subgroup.centralizer
      ((L.subgroupOf X : Subgroup ↥X) : Set ↥X))) : Q3NM.AutOddFree ↥L := by
  set N : Subgroup ↥X := Subgroup.centralizer ((L.subgroupOf X : Subgroup ↥X) : Set ↥X) with hN
  have hs := isSimpleGroup_of_centOmega3 h
  let π : ↥X →* (↥X ⧸ N) ⧸ Subgroup.center (↥X ⧸ N) :=
    (QuotientGroup.mk' _).comp (QuotientGroup.mk' N)
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  let φ : ↥L →* (↥X ⧸ N) ⧸ Subgroup.center (↥X ⧸ N) := π.comp (Subgroup.inclusion hLX)
  have hφ1 : ¬ ∀ l : ↥L, φ l = 1 := by
    intro h1
    have hc : ∀ l l' : ↥L, ⁅l, l'⁆ ∈ Subgroup.center ↥L := by
      intro l l'
      have h1l : QuotientGroup.mk' (Subgroup.center (↥X ⧸ N))
          (QuotientGroup.mk' N (Subgroup.inclusion hLX l)) = 1 := h1 l
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1l
      have hcN : ⁅Subgroup.inclusion hLX l, Subgroup.inclusion hLX l'⁆ ∈ N := by
        rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
          commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp h1l _).symm
      rw [Subgroup.mem_center_iff]
      intro m
      have hm := Subgroup.mem_centralizer_iff.mp hcN (Subgroup.inclusion hLX m)
        (Subgroup.mem_subgroupOf.mpr m.2)
      rw [← map_commutatorElement, ← map_mul, ← map_mul] at hm
      exact Subgroup.inclusion_injective hLX hm
    have hZ : Subgroup.center ↥L = ⊤ := by
      have hle : commutator ↥L ≤ Subgroup.center ↥L :=
        Subgroup.commutator_le.mpr fun g _ g' _ => hc g g'
      rw [hL.1.1.commutator_eq_top] at hle
      exact top_le_iff.mp hle
    obtain ⟨a, b, hab⟩ := hL.1.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    have ha' : a' ∈ Subgroup.center ↥L := by
      rw [hZ]
      exact Subgroup.mem_top a'
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp ha' b']
  have hφs : Function.Surjective φ := by
    have hn : φ.range.Normal := by
      have e : φ.range = (L.subgroupOf X).map π := by
        ext q
        constructor
        · rintro ⟨l, rfl⟩
          exact ⟨Subgroup.inclusion hLX l, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
      rw [e]
      exact hLn.map π hπ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.range with hb | ht
    · exfalso
      refine hφ1 fun l => ?_
      have hl : φ l ∈ φ.range := ⟨l, rfl⟩
      rwa [hb, Subgroup.mem_bot] at hl
    · exact MonoidHom.range_eq_top.mp ht
  have hker : φ.ker ≤ Subgroup.center ↥L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hL.1 φ.normal_ker with ht | hle
    · exact absurd (fun l => (MonoidHom.mem_ker).mp (ht ▸ Subgroup.mem_top l)) hφ1
    · exact hle
  have : Group.IsPerfect ↥L := hL.1.1
  have hZ : Subgroup.center ((↥X ⧸ N) ⧸ Subgroup.center (↥X ⧸ N)) = ⊥ :=
    Vtx.center_quot_center_eq_bot hs
  let e : ↥L ⧸ Subgroup.center ↥L ≃* (↥X ⧸ N) ⧸ Subgroup.center (↥X ⧸ N) :=
    (Q3NM.centralQuotientIso φ hφs hker).trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  exact Vtx.autOddFree_of_quot_center hL.1.1 ((hOm _ h).of_mulEquiv e.symm)

section Twin

variable {Q : Type} [Group Q] [Finite Q] {Φ : Set (Subgroup Q)} {n : ℕ}

theorem not_twinFreeAt_of_central (h4 : Thm4RBelow 3 n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {L : Subgroup Q}
    (hL : IsComponent L) {K J : Subgroup Q} (hK : K ∈ Φ) (hJ : J ∈ Φ) {a b : Q}
    (ha : IsUniqueInvolution K a) (hb : IsUniqueInvolution J b)
    (hc : b * a⁻¹ ∈ Subgroup.center Q) (hne : a ≠ b) (hm : ∃ y ∈ L, a * y ≠ y * a) :
    ¬ Vtx.TwinFreeAt Φ K a L := by
  obtain ⟨y, hy, hay⟩ := hm
  have hby : b * y ≠ y * b := by
    intro e
    apply hay
    have hcy : b * a⁻¹ * y = y * (b * a⁻¹) := (Subgroup.mem_center_iff.mp hc y).symm
    calc a * y = (b * a⁻¹)⁻¹ * (b * y) := by group
      _ = (b * a⁻¹)⁻¹ * (y * (b * a⁻¹) * a) := by rw [e]; group
      _ = (b * a⁻¹)⁻¹ * (b * a⁻¹ * y * a) := by rw [← hcy]
      _ = y * a := by group
  obtain ⟨g, hg, hgK⟩ := Vtx.exists_conj_of_moves h4 h hO hn hL hK hJ ⟨a, ha.mem, y, hy, hay⟩
    ⟨b, hb.mem, y, hy, hby⟩
  have hgab : g * a * g⁻¹ = b := by
    have h1 := ha.conj g
    rw [hgK] at h1
    exact h1.eq hb
  intro htf
  have h2 : g * a * g⁻¹ = a := htf g hg fun l _ => by
    rw [hgab]
    exact (Subgroup.mem_center_iff.mp hc l).symm
  rw [hgab] at h2
  exact hne h2.symm


theorem twinOutcomeE (h4 : Thm4RBelow 3 n) (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n)
    (hA : CIT3Below n) (h : TypeRFam 3 Φ) (hO : classicalInvolutionOddCore Q = ⊥)
    (hn : Nat.card Q < n) {K : Subgroup Q} (hK : K ∈ Φ) {z : Q} (hz : IsUniqueInvolution K z)
    {L : Subgroup Q} (hL : IsComponent L) (hm : ∃ y ∈ L, z * y ≠ y * z)
    (hLn : (L.subgroupOf (Vtx.orbGrp Φ K)).Normal) (htf : ¬ Vtx.TwinFreeAt Φ K z L) :
    PhilipHall.Frame.TwinE4 ↥(Vtx.orbGrp Φ K) ∨
      PhilipHall.Frame.CentOmega3 (↥(Vtx.orbGrp Φ K) ⧸ Subgroup.centralizer
        ((L.subgroupOf (Vtx.orbGrp Φ K) : Subgroup ↥(Vtx.orbGrp Φ K)) :
          Set ↥(Vtx.orbGrp Φ K))) := by
  have hcl := h.hyp.conjInvariant
  obtain ⟨S', hd', hc'⟩ := Vtx.tightCls_orbGrp h4 h hO hn hK hz
  have hNc := Vtx.centralizer_subgroupOf_le_center h4 h hO hn hK hz hL hm
  have hN2 := Vtx.isPGroup_centralizer_subgroupOf h4 h hO hn hK hz hL hm
  obtain ⟨y₀, hy₀, hne₀⟩ := hm
  have hLX : L ≤ Vtx.orbGrp Φ K := Vtx.le_orbGrp_of_moves hcl hK hL ⟨z, hz.mem, y₀, hy₀, hne₀⟩
  have hKX : K ≤ Vtx.orbGrp Φ K := Vtx.le_orbGrp K
  set N := Subgroup.centralizer ((L.subgroupOf (Vtx.orbGrp Φ K) : Subgroup ↥(Vtx.orbGrp Φ K)) :
    Set ↥(Vtx.orbGrp Φ K)) with hNdef
  have : N.Normal := Subgroup.normal_centralizer
  have hmemN : ∀ w : ↥(Vtx.orbGrp Φ K), (∀ l ∈ L, (w : Q) * l = l * w) → w ∈ N := by
    intro w hw
    rw [hNdef, Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subtype.ext (hw l (Subgroup.mem_subgroupOf.mp hl)).symm
  have htN : (⟨z, hKX hz.mem⟩ : ↥(Vtx.orbGrp Φ K)) ∉ N := by
    intro hzN
    exact hne₀ (congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hzN ⟨y₀, hLX hy₀⟩ (Subgroup.mem_subgroupOf.mpr hy₀))).symm
  simp only [Vtx.TwinFreeAt, not_forall] at htf
  obtain ⟨g, hg, hgL, hgz⟩ := htf
  set w : ↥(Vtx.orbGrp Φ K) := ⟨g, hg⟩ * ⟨z, hKX hz.mem⟩ * ⟨g, hg⟩⁻¹ * ⟨z, hKX hz.mem⟩⁻¹
    with hwdef
  have hwN : w ∈ N := hmemN w hgL
  have hw1 : w ≠ 1 := by
    intro h1
    apply hgz
    have h2 : (w : Q) = 1 := congrArg Subtype.val h1
    simp only [hwdef, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    calc g * z * g⁻¹ = g * z * g⁻¹ * z⁻¹ * z := by group
      _ = z := by rw [h2, one_mul]
  have hy : (⟨g, hg⟩ : ↥(Vtx.orbGrp Φ K)) * ⟨z, hKX hz.mem⟩ * ⟨g, hg⟩⁻¹ =
      ⟨z, hKX hz.mem⟩ * w := by
    have hwz : w * ⟨z, hKX hz.mem⟩ = ⟨z, hKX hz.mem⟩ * w :=
      (Subgroup.mem_center_iff.mp (hNc hwN) _).symm
    calc (⟨g, hg⟩ : ↥(Vtx.orbGrp Φ K)) * ⟨z, hKX hz.mem⟩ * ⟨g, hg⟩⁻¹ =
        w * ⟨z, hKX hz.mem⟩ := by rw [hwdef]; group
      _ = ⟨z, hKX hz.mem⟩ * w := hwz
  have hq := PhilipHall.QuaternionBridge.q8Quot_of_twin hd' hc' hNc hN2 htN hwN hw1 hy
  have hAE := PhilipHall.QuaternionBridge.aEmpty_map' hd' hc'.1 hNc hN2 htN
  have hcard : Nat.card (↥(Vtx.orbGrp Φ K) ⧸ N) < n :=
    lt_of_lt_of_le hq.card_lt ((Subgroup.card_le_card_group _).trans hn.le)
  rcases htw.hasLift hcard hq.datum hq.cls.1 hq.cls.2.1 hq.cls.2.2 hq.hyp hAE hq.twin with
    hE2 | hE4 | hlift
  · exact absurd (TwistQ.inO2_of hN2 hE2)
      (Vtx.not_tightInO2_orbGrp hcl hK hz hL ⟨y₀, hy₀, hne₀⟩)
  · obtain ⟨Q', _, f, hfs, hf2, hQ'⟩ := hE4
    refine Or.inl ⟨Q', inferInstance, f.comp (QuotientGroup.mk' N),
      hfs.comp (QuotientGroup.mk'_surjective N), ?_, hQ'⟩
    rw [← MonoidHom.comap_ker]
    exact hf2.comap_of_ker_isPGroup _ (by rw [QuotientGroup.ker_mk']; exact hN2)
  · exact Or.inr (TQ.centOmega3_of_hasLift hA hcard hq.datum hq.cls.2.1 hq.cls.2.2 hq.hyp hAE
      hq.twin hlift)

theorem autOddFree_of_not_twinFree (h4 : Thm4RBelow 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hA : CIT3Below n)
    (hOm : OmegaAutOddFreeR) (h : TypeRFam 3 Φ) (hO : classicalInvolutionOddCore Q = ⊥)
    (hn : Nat.card Q < n) {K : Subgroup Q} (hK : K ∈ Φ) {z : Q} (hz : IsUniqueInvolution K z)
    {L : Subgroup Q} (hL : IsComponent L) (hm : ∃ y ∈ L, z * y ≠ y * z)
    (htf : ¬ Vtx.TwinFreeAt Φ K z L) : Q3NM.AutOddFree ↥L := by
  have hLn := Vtx.normal_subgroupOf_orbGrp h4 h hO hn hK hz hL hm
  obtain ⟨y₀, hy₀, hne₀⟩ := hm
  have hLX := Vtx.le_orbGrp_of_moves h.hyp.conjInvariant hK hL ⟨z, hz.mem, y₀, hy₀, hne₀⟩
  rcases twinOutcomeE h4 htw hA h hO hn hK hz hL ⟨y₀, hy₀, hne₀⟩ hLn htf with hT | hΩ3
  · exact Vtx.autOddFree_of_quot_center hL.1.1
      (Vtx.autOddFree_of_exLie (Vtx.exLie_of_twinE4 hLX hLn hL hT))
  · exact autOddFree_of_centOmega3 hOm hLX hLn hL hΩ3

end Twin

section Vertex

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {n : ℕ}


theorem hyp51At_of_twinPair (h4 : Thm4RBelow 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hOm : OmegaAutOddFreeR)
    (hA : CIT3Below n) (hZ : Subgroup.center G = ⊥) (hGn : Nat.card G ≤ n)
    (hΩ : TypeRFam 3 Ω) {B : Subgroup G} (hB : IsElemAbelian 2 B) {a b c : G} (haB : a ∈ B)
    (hcB : c ∈ B) (hc1 : c ≠ 1) (ha1 : a ≠ 1) (hac : a ≠ c) (habc : a * b = c)
    {Ma Mb : Subgroup G} (hMa : XMem Ω c Ma) (hMb : XMem Ω c Mb)
    (ha : IsUniqueInvolution Ma a) (hb : IsUniqueInvolution Mb b) : Hyp51At B c := by
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ B, x * x = 1 := fun x hx => (sq x).symm.trans (hB.2 x hx)
  have hac' : a * c = c * a := hBc a haB c hcB
  have haC : a ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hac'
  have hbe : b = a * c := by
    calc b = a * (a * b) := by rw [← mul_assoc, hsq a haB, one_mul]
      _ = a * c := by rw [habc]
  have hcC : c ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hbC : b ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [hbe]
    exact Subgroup.mul_mem _ haC hcC
  have hΦ : TypeRFam 3 (vtxFam Ω c) := hΩ.vtxFam
  have hO := oddQuot_oddCore_eq_bot c
  have hQn : Nat.card (OddQuot c) < n := lt_of_lt_of_le (natCard_oddQuot_lt hZ hc1) hGn
  have hKa := modOdd_coreAt_mem_vtxFam hMa
  have hKb := modOdd_coreAt_mem_vtxFam hMb
  have haz := isUniqueInvolution_modOdd_coreAt hΩ hMa ha haC
  have hbz := isUniqueInvolution_modOdd_coreAt hΩ hMb hb hbC
  have haB' := oddQuotMk_mem_modOdd haB haC
  have haZ := Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 haB ha1 hac haC
  have hba : (⟨b, hbC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) * ⟨a, haC⟩⁻¹ = ⟨c, hcC⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hbe]
    calc a * c * a⁻¹ = c * a * a⁻¹ := by rw [hac']
      _ = c := by group
  have hcZ : oddQuotMk c ⟨c, hcC⟩ ∈ Subgroup.center (OddQuot c) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective _ y
    change oddQuotMk c k * oddQuotMk c _ = oddQuotMk c _ * oddQuotMk c k
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp k.2)
  have hc' : oddQuotMk c ⟨b, hbC⟩ * (oddQuotMk c ⟨a, haC⟩)⁻¹ ∈ Subgroup.center (OddQuot c) := by
    rw [← map_inv, ← map_mul, hba]
    exact hcZ
  have hne : oddQuotMk c ⟨a, haC⟩ ≠ oddQuotMk c ⟨b, hbC⟩ := by
    intro e
    have h1 : oddQuotMk c ⟨c, hcC⟩ = 1 := by
      rw [← hba, map_mul, map_inv, ← e, mul_inv_cancel]
    exact hc1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext (hsq c hcB)) h1))
  refine hyp51At_of_moved hsq hBc ⟨oddQuotMk c ⟨a, haC⟩, haB', haZ,
    fun L₁ L₂ hL₁ hL₂ hm₁ hm₂ => Vtx.moves_atMostOne h4 hΦ hO hQn hKa haz hL₁ hL₂ hm₁ hm₂⟩ ?_
  intro L hL hm x _ _ _
  have hma := hm _ haB' haZ
  exact (autOddFree_of_not_twinFree h4 htw hA hOm hΦ hO hQn hKa haz hL hma
    (not_twinFreeAt_of_central h4 hΦ hO hQn hL hKa hKb haz hbz hc' hne hma)).on _

end Vertex

end CFSG.ClassicalInvolution.Q3.TL4
