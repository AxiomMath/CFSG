module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93Facts
public import CFSG.GroupTheory.PLayer.CenterQuotientAction
public import CFSG.GroupTheory.PerfectCoverProduct
public import CFSG.GroupTheory.PerfectLeSupCenter
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdSchur
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TStdCovDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Row40
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
public import CFSG.LocalAnalysis.GLTheoremA.S11.Lemma119

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FStdDiag

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind)
open CFSG.LocalAnalysis.GLTheoremA.HStdExcl (SmallOrd)

theorem fstd_card_of_isA6 {S : Type} [Group S] (h : catalogIs S S10.isA6) : Nat.card S = 360 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | alternating n hn =>
    simp only [S10.isA6] at hi
    subst hi
    rw [CFSG.LocalAnalysis.GLTheoremA.CatDistinct.card_alternating_of_iso
      (n := 6) (by norm_num : 5 ≤ 6) e]
    norm_num [Nat.factorial]
  | cyclic _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie _ => exact hi.elim

theorem fstd_card_pSimple_of_smallType {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (h : SmallType 3 K) :
    Nat.card (PSimple 3 K) = 25920 ∨ Nat.card (PSimple 3 K) = 360 := by
  rcases h with hU | hA
  · exact Or.inl (CFSG.LocalAnalysis.GLTheoremA.CatB.U48.card_of_isU4two hU)
  · exact Or.inr (fstd_card_of_isA6 hA)

theorem fstd_pSimple_equiv {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK : CFSG.Open.IsQuasisimple ↥K) (h : SmallType 3 K) :
    Nonempty (PSimple 3 K ≃* (↥K ⧸ Subgroup.center ↥K)) := by
  refine hstd_pSimple_equiv_center hK (hstd_ne_top_of_one_lt ?_)
  rcases fstd_card_pSimple_of_smallType h with h1 | h1 <;> rw [h1] <;> norm_num

theorem fstd_card_centerQuot_of_smallType {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK : CFSG.Open.IsQuasisimple ↥K) (h : SmallType 3 K) :
    Nat.card (↥K ⧸ Subgroup.center ↥K) = 25920 ∨ Nat.card (↥K ⧸ Subgroup.center ↥K) = 360 := by
  obtain ⟨e⟩ := fstd_pSimple_equiv hK h
  rw [← Nat.card_congr e.toEquiv]
  exact fstd_card_pSimple_of_smallType h

theorem fstd_three_dvd_card {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK : CFSG.Open.IsQuasisimple ↥K) (h : SmallType 3 K) : 3 ∣ Nat.card ↥K := by
  have hdvd : Nat.card (↥K ⧸ Subgroup.center ↥K) ∣ Nat.card ↥K :=
    Subgroup.card_quotient_dvd_card _
  rcases fstd_card_centerQuot_of_smallType hK h with h1 | h1 <;> rw [h1] at hdvd <;>
    exact dvd_trans (by norm_num) hdvd

section Image

variable {X : Type} [Group X] [Finite X] {L B : Subgroup X}

theorem fstd_phi_ne_one (hL : CFSG.Open.IsQuasisimple ↥L)
    (hBN : B ≤ Subgroup.normalizer (L : Set X)) (b : ↥B)
    (hbL : (b : X) ∉ Subgroup.centralizer (L : Set X)) :
    normalizerToCenterQuotientAut L B hBN b ≠ 1 := by
  intro h
  exact hbL ((normalizerToCenterQuotientAut_eq_one_iff ⟨hL.1⟩ hBN b).1 h).2

theorem fstd_image (hL : CFSG.Open.IsQuasisimple ↥L) (hBN : B ≤ Subgroup.normalizer (L : Set X))
    {d : X} (hdB : d ∈ B) {K : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K (L ⊓ Subgroup.centralizer ({d} : Set X))) :
    CFSG.Open.IsComponentOf ((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))
        (fixSubgroup (normalizerToCenterQuotientAut L B hBN ⟨d, hdB⟩)) ∧
      Nonempty (↥((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ⧸
        Subgroup.center ↥((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ≃*
          ↥K ⧸ Subgroup.center ↥K) := by
  classical
  let Q := ↥L
  let Z : Subgroup Q := Subgroup.center Q
  let π : Q →* Q ⧸ Z := QuotientGroup.mk' Z
  let γ : MulAut Q := normalizerConjAutOfMem L B hBN ⟨d, hdB⟩
  let γbar : MulAut (Q ⧸ Z) := normalizerToCenterQuotientAut L B hBN ⟨d, hdB⟩
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker ≤ Subgroup.center Q := by
    rw [show π.ker = Subgroup.center Q from QuotientGroup.ker_mk' _]
  have hcomp : ∀ k : Q, π (γ k) = γbar (π k) := fun k =>
    normalizerConjAutOfMem_comp_mk L B hBN ⟨d, hdB⟩ k
  let K' : Subgroup Q := K.subgroupOf L
  have hKL : K ≤ L := hK.1.trans inf_le_left
  have hK'qs : CFSG.Open.IsQuasisimple ↥K' :=
    hK.2.2.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL)
  have hγeq : γ = (Subgroup.normalizerMonoidHom (H := L)) ⟨d, hBN hdB⟩ := rfl
  have hmemK' : ∀ k : ↥K', (k : Q) ∈ fixSubgroup γ := by
    intro k
    rw [mem_fixSubgroup]
    apply Subtype.ext
    have hkK : ((k : Q) : X) ∈ K := k.2
    have hkC : ((k : Q) : X) ∈ Subgroup.centralizer ({d} : Set X) :=
      (Subgroup.mem_inf.1 (hK.1 hkK)).2
    have hcomm : ((k : Q) : X) * d = d * ((k : Q) : X) :=
      Subgroup.mem_centralizer_singleton_iff.1 hkC
    have hval : (((normalizerConjAutOfMem L B hBN ⟨d, hdB⟩) k : Q) : X) =
        d * ((k : Q) : X) * d⁻¹ := by
      simp [normalizerConjAutOfMem]
    rw [hval, ← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hK'le : K' ≤ fixSubgroup γ := fun k hk => hmemK' ⟨k, hk⟩
  have hK'sub : IsSubnormal K' (fixSubgroup γ) := by
    have hfixmap : (fixSubgroup γ).map L.subtype =
        L ⊓ Subgroup.centralizer ({d} : Set X) := by
      rw [hγeq]
      exact CFSG.map_eqLocus_normalizerMonoidHom L (hBN hdB)
    have hcomap : (L ⊓ Subgroup.centralizer ({d} : Set X)).comap L.subtype = fixSubgroup γ := by
      rw [← hfixmap]
      exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective (fixSubgroup γ)
    have h := hK.2.1.comap L.subtype
    rw [show K.comap L.subtype = K' from rfl, hcomap] at h
    exact h
  let J : Subgroup (Q ⧸ Z) := K'.map π
  have hK'notZ : ¬ K' ≤ π.ker := by
    intro hle
    have hZQ : K' ≤ Subgroup.center Q := by
      rwa [show π.ker = Subgroup.center Q from QuotientGroup.ker_mk' _] at hle
    have hcenter_top : Subgroup.center ↥K' = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_center_iff.1 (hZQ x.2) (y : Q)
    haveI : Subsingleton (↥K' ⧸ Subgroup.center ↥K') := by
      rw [hcenter_top]
      exact QuotientGroup.subsingleton_quotient_top
    haveI : Nontrivial (↥K' ⧸ Subgroup.center ↥K') := hK'qs.2.toNontrivial
    exact not_subsingleton _ ‹Subsingleton (↥K' ⧸ Subgroup.center ↥K')›
  have hJqs : CFSG.Open.IsQuasisimple ↥J := by
    have hrange : (π.comp K'.subtype).range = J := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hkerne : (π.comp K'.subtype).ker ≠ ⊤ := by
      intro htop
      apply hK'notZ
      intro k hk
      have hk' : (⟨k, hk⟩ : ↥K') ∈ (π.comp K'.subtype).ker := by rw [htop]; trivial
      exact hk'
    rw [← hrange]
    exact CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top
      hK'qs (π.comp K'.subtype) hkerne
  have hJsub : IsSubnormal J (fixSubgroup γbar) := by
    have h1 : IsSubnormal J ((fixSubgroup γ).map π) := hK'sub.map π
    have hnormal : (((fixSubgroup γ).map π).subgroupOf (fixSubgroup γbar)).Normal :=
      normal_map_fixSubgroup π hker γ γbar hcomp hπsurj
    have h2 : IsSubnormal ((fixSubgroup γ).map π) (fixSubgroup γbar) :=
      CFSG.Open.IsSubnormal.step (H := (fixSubgroup γ).map π) (M := fixSubgroup γbar)
        (K := fixSubgroup γbar) (map_fixSubgroup_le π hker γ γbar hcomp) hnormal
        (CFSG.Open.IsSubnormal.refl _)
    exact h1.trans h2
  refine ⟨⟨hJsub.le, hJsub, hJqs⟩, ?_⟩
  have hψkerZ : (π.subgroupMap K').ker ≤ Subgroup.center ↥K' := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxZ : (x : Q) ∈ Subgroup.center Q := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center Q)]
      exact congrArg Subtype.val hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hxZ (y : Q)
  obtain ⟨eJq⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
    hK'qs.1 (π.subgroupMap K') (π.subgroupMap_surjective K') hψkerZ
  let eKK' : ↥K' ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKL
  let eKK'q : ↥K' ⧸ Subgroup.center ↥K' ≃* ↥K ⧸ Subgroup.center ↥K :=
    QuotientGroup.congr (Subgroup.center ↥K') (Subgroup.center ↥K) eKK'
      (Subgroup.map_center_eq eKK')
  exact ⟨eJq.symm.trans eKK'q⟩

theorem fstd_mem_center_of_image {K : Subgroup X} (hKL : K ≤ L)
    (hI : Subgroup.center ↥((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) = ⊥) :
    ∀ z ∈ K, (∀ k ∈ K, k * z = z * k) → ∀ l ∈ L, l * z = z * l := by
  intro z hz hzc l hl
  let π : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' _
  let z' : ↥L := ⟨z, hKL hz⟩
  have hz'K : z' ∈ K.subgroupOf L := hz
  let w : ↥((K.subgroupOf L).map π) := ⟨π z', Subgroup.mem_map_of_mem π hz'K⟩
  have hw : w ∈ Subgroup.center ↥((K.subgroupOf L).map π) := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨_, k, hk, rfl⟩
    apply Subtype.ext
    show π k * π z' = π z' * π k
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hzc (k : X) hk
  rw [hI] at hw
  have hw1 : π z' = 1 := congrArg Subtype.val (Subgroup.mem_bot.1 hw)
  have hz'Z : z' ∈ Subgroup.center ↥L := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center ↥L)]
    exact hw1
  have := Subgroup.mem_center_iff.1 hz'Z ⟨l, hl⟩
  exact congrArg Subtype.val this

end Image

section Marking

variable {X : Type} [Group X] [Finite X] {L B : Subgroup X}

theorem fstd_innDiagKind (hL : CFSG.Open.IsQuasisimple ↥L)
    (hBN : B ≤ Subgroup.normalizer (L : Set X)) (hidm : InnerDiagMarking B L) :
    ∃ labK : GLALabel, ∀ b : ↥B,
      InnDiagKind (↥L ⧸ Subgroup.center ↥L) labK (normalizerToCenterQuotientAut L B hBN b) := by
  have hcen : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.center_centerQuot_eq_bot hL
  haveI : Group.IsPerfect ↥L := ⟨hL.1⟩
  have hS : commutator (↥L ⧸ Subgroup.center ↥L) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center ↥L))
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  obtain ⟨-, lab, hlam, hraw⟩ := hidm
  refine ⟨lab, fun b => ⟨hS, lab, hlam,
    CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩⟩
  rintro R _ I F ⟨hs, hna, θ, -, hall⟩
  obtain ⟨φ, hφ, hind⟩ := hall ((b : X)⁻¹) (B.inv_mem b.2)
  refine ⟨hs, hna, (CanonInn.quotCenterEquivOfBot hcen).trans θ, rfl, φ, hφ, ?_⟩
  intro s s' hss'
  subst hss'
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective s
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, CanonInn.quotCenterEquivOfBot_mk,
    CanonInn.quotCenterEquivOfBot_mk]
  have hmk : normalizerToCenterQuotientAut L B hBN b (QuotientGroup.mk l) =
      QuotientGroup.mk (normalizerConjAutOfMem L B hBN b l) :=
    (normalizerConjAutOfMem_comp_mk L B hBN b l).symm
  rw [hmk]
  apply hind l
  simp [normalizerConjAutOfMem]

theorem fstd_isElemAbelian_range (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hBN : B ≤ Subgroup.normalizer (L : Set X)) :
    CFSG.Assembly.IsElemAbelian 3 (normalizerToCenterQuotientAut L B hBN).range := by
  refine ⟨⟨⟨fun a c => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 c.2
    apply Subtype.ext
    have hxz : x * z = z * x := hB.1.is_comm.comm x z
    simp only [Subgroup.coe_mul]
    rw [← hx, ← hz, ← map_mul, ← map_mul, hxz]
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    have hx : x ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hB.2 _ x.2, Subgroup.coe_one])
    rw [← map_pow, hx, map_one]

theorem fstd_card_range (hL : CFSG.Open.IsQuasisimple ↥L)
    (hBN : B ≤ Subgroup.normalizer (L : Set X)) :
    Nat.card ↥(normalizerToCenterQuotientAut L B hBN).range *
        Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) = Nat.card ↥B := by
  set φ := normalizerToCenterQuotientAut L B hBN
  have hker : φ.ker = (B ⊓ Subgroup.centralizer (L : Set X)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact normalizerToCenterQuotientAut_eq_one_iff ⟨hL.1⟩ hBN b
  have hk : Nat.card ↥φ.ker = Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← hk, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

end Marking

section Centre

variable {X : Type} [Group X] [Finite X] {L K B : Subgroup X} {d : X}

theorem fstd_ne_top_of_small (hL : CFSG.Open.IsQuasisimple ↥L)
    (hK : CFSG.Open.IsComponentOf K (L ⊓ Subgroup.centralizer ({d} : Set X)))
    (hs : SmallType 3 K) : GLAPPrimeCore 3 ↥L ≠ ⊤ := by
  have hKL : K ≤ L := hK.1.trans inf_le_left
  have h3L : 3 ∣ Nat.card ↥L :=
    dvd_trans (fstd_three_dvd_card hK.2.2 hs) (Subgroup.card_dvd_of_le hKL)
  intro htop
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card ↥L) := by
    have h := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥L)
    have htop' : CFSG.pPrimeCore 3 ↥L = ⊤ := htop
    rw [htop'] at h
    simpa using h
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop h3L

theorem fstd_smallConcl (h : SmallCentreS) (hL : CFSG.Open.IsQuasisimple ↥L)
    (hchev : IsChevSimple 2 (PSimple 3 L)) (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hBc : 3 ^ 4 ≤ Nat.card ↥B) (hidm : InnerDiagMarking B L)
    (hCB : Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set X)) = 3) (hdB : d ∈ B)
    (hdL : d ∉ Subgroup.centralizer (L : Set X))
    (hK : CFSG.Open.IsComponentOf K (L ⊓ Subgroup.centralizer ({d} : Set X)))
    (hs : SmallType 3 K) :
    SmallConcl ((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ∧
      Nonempty (↥((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ⧸
        Subgroup.center ↥((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ≃*
          ↥K ⧸ Subgroup.center ↥K) := by
  have hBN : B ≤ Subgroup.normalizer (L : Set X) := S11.le_normalizer_of_innerDiag hidm
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2
  have hnab : ∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hL
  obtain ⟨eL0⟩ := hstd_pSimple_equiv_center hL (fstd_ne_top_of_small hL hK hs)
  have hchevS : IsChevSimple 2 (↥L ⧸ Subgroup.center ↥L) :=
    List93.isChevSimple_of_mulEquiv eL0 hchev
  obtain ⟨labK, hlab⟩ := fstd_innDiagKind hL hBN hidm
  have hAcard : 27 ≤ Nat.card ↥(normalizerToCenterQuotientAut L B hBN).range := by
    have h1 := fstd_card_range hL hBN
    rw [hCB] at h1
    omega
  have hAkind : ∀ β ∈ (normalizerToCenterQuotientAut L B hBN).range,
      InnDiagKind (↥L ⧸ Subgroup.center ↥L) labK β := by
    rintro _ ⟨b, rfl⟩
    exact hlab b
  obtain ⟨hIcomp, ⟨eI⟩⟩ := fstd_image hL hBN hdB hK
  have hsmallI : SmallOrd ((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) := by
    unfold SmallOrd
    rw [Nat.card_congr eI.toEquiv]
    exact fstd_card_centerQuot_of_smallType hK.2.2 hs
  exact ⟨h _ inferInstance hnab hchevS labK _ (fstd_isElemAbelian_range hB hBN) hAcard hAkind _
    ⟨⟨d, hdB⟩, rfl⟩ (fstd_phi_ne_one hL hBN ⟨d, hdB⟩ hdL) _ hIcomp hsmallI, ⟨eI⟩⟩

theorem stdCovDiagCentreAt_of_S (h : SmallCentreS) : StdCovDiagCentreAt := by
  intro X _ _ L K B d hL hchev hB hBc hidm hCB hdB hdL hK hs
  exact fstd_mem_center_of_image (hK.1.trans inf_le_left)
    (fstd_smallConcl h hL hchev hB hBc hidm hCB hdB hdL hK hs).1.1

end Centre

section Odd

variable {X : Type} [Group X] [Finite X]

theorem fstd_exists_noncomm {G : Type*} [Group G] (h : CFSG.Open.IsQuasisimple G) :
    ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
    G h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h' => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h'])⟩

theorem fstd_card_center_dvd_two
    {K : Subgroup X} (hK : CFSG.Open.IsQuasisimple ↥K) (hU : U42Type 3 K) :
    Nat.card ↥(Subgroup.center ↥K) ∣ 2 := by
  obtain ⟨q, hv, hq, ⟨eU⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isU4two hU
  have hcard : 1 < Nat.card (PSimple 3 K) := by
    rw [Nat.card_congr eU.toEquiv, hstd_card_U42 (hv := hv) hq]
    norm_num
  obtain ⟨eK⟩ := hstd_pSimple_equiv_center hK (hstd_ne_top_of_one_lt hcard)
  have e : (↥K ⧸ Subgroup.center ↥K) ≃* CFSG.HardMathSupport.Dickson.I271.Amb.U4Group q hv :=
    eK.symm.trans eU
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.U42.multiplier_PSU_four_two
    (CFSG.HardMathSupport.Dickson.I271.Amb.U4Group q hv)
    (CFSG.HardMathSupport.Dickson.I271.Amb.u4_lieModel (hv := hv) hq)
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier ⟨hK.1⟩ e
  rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at hdvd
  exact hdvd

theorem fstd_cover {L : Subgroup X} (H : Subgroup (↥L ⧸ Subgroup.center ↥L))
    (hHs : IsSimpleGroup ↥H) (hHnc : ∃ a b : ↥H, a * b ≠ b * a) (hH3 : ThreeFreeMult ↥H) :
    ∃ M : Subgroup ↥L, Nat.Coprime 3 (Nat.card ↥(Subgroup.center ↥M)) ∧
      ∀ P : Subgroup ↥L, ⁅P, P⁆ = P → P.map (QuotientGroup.mk' (Subgroup.center ↥L)) ≤ H →
        P ≤ M := by
  classical
  haveI : IsSimpleGroup ↥H := hHs
  let Q := ↥L
  let Z : Subgroup Q := Subgroup.center Q
  let π : Q →* Q ⧸ Z := QuotientGroup.mk' Z
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker ≤ Subgroup.center Q := by
    rw [show π.ker = Subgroup.center Q from QuotientGroup.ker_mk' _]
  have hHperf : Group.IsPerfect ↥H := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hHnc).1.1
  have hHcomm : ⁅H, H⁆ = H := Subgroup.isPerfect_iff.mp hHperf
  have hHZ : Subgroup.center ↥H = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hHnc).2
  let P0 : Subgroup Q := H.comap π
  let M : Subgroup Q := ⁅P0, P0⁆
  have hMmap : M.map π = H := CFSG.GroupTheory.PerfectCover.map_commutator_comap π hπsurj hHcomm
  have hMperf : Group.IsPerfect ↥M :=
    CFSG.GroupTheory.PerfectCover.isPerfect_commutator_comap π hπsurj hker hHcomm
  have hZP : Z ≤ P0 := by
    intro z hz
    rw [Subgroup.mem_comap]
    have hz1 : π z = 1 := by
      have hz' : z ∈ π.ker := by rwa [show π.ker = Z from QuotientGroup.ker_mk' _]
      exact hz'
    rw [hz1]
    exact Subgroup.one_mem _
  have hMP : M ≤ P0 := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hP_eq : P0 = M ⊔ Z := by
    apply le_antisymm
    · intro p hp
      obtain ⟨q, hq, z, hz, hpq⟩ :=
        CFSG.GroupTheory.PerfectCover.exists_mul_of_mem_comap π hπsurj hHcomm hp
      have hzZ : z ∈ Z := by
        rw [show π.ker = Z from QuotientGroup.ker_mk' _] at hz
        exact hz
      rw [hpq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hzZ)
    · exact sup_le hMP hZP
  let ψ : ↥M →* ↥H :=
    (π.comp M.subtype).codRestrict H (fun m => by
      have hm : π (m : Q) ∈ M.map π := Subgroup.mem_map_of_mem π m.2
      rwa [hMmap] at hm)
  have hψsurj : Function.Surjective ψ := by
    intro l
    have hl : (l : Q ⧸ Z) ∈ M.map π := by rw [hMmap]; exact l.2
    obtain ⟨m, hm, hml⟩ := hl
    exact ⟨⟨m, hm⟩, Subtype.ext hml⟩
  have hψker : ψ.ker ≤ Subgroup.center ↥M := by
    intro m hm
    rw [MonoidHom.mem_ker] at hm
    have hmZ : (m : Q) ∈ Z := by
      have h1 : π (m : Q) = 1 := congrArg Subtype.val hm
      rw [← QuotientGroup.ker_mk' Z]
      exact h1
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hmZ (y : Q)
  obtain ⟨eM⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
    hMperf.commutator_eq_top ψ hψsurj hψker
  let eH : ↥H ⧸ Subgroup.center ↥H ≃* ↥H :=
    (QuotientGroup.quotientMulEquivOfEq hHZ).trans QuotientGroup.quotientBot
  let eMH : ↥M ⧸ Subgroup.center ↥M ≃* ↥H := eM.trans eH
  have hMqs : CFSG.Open.IsQuasisimple ↥M := by
    refine ⟨hMperf.commutator_eq_top, eMH.isSimpleGroup⟩
  refine ⟨M, hH3 ↥M hMqs ⟨eMH⟩, fun P hP hPH => ?_⟩
  have hPP0 : P ≤ P0 := by
    rw [← Subgroup.map_le_iff_le_comap]
    exact hPH
  have hMperfSub : ⁅M, M⁆ = M := Subgroup.isPerfect_iff.mp hMperf
  exact CFSG.le_of_perfect_of_le_sup_center hMperfSub hP (hPP0.trans (le_of_eq hP_eq))

theorem stdCovDiagOddAt_of_S
    (h : SmallCentreS) : StdCovDiagOddAt := by
  intro X _ _ L K B d hL hchev hB hBc hidm hCB hdB hdL hK hs
  obtain ⟨⟨hZI, hA6⟩, ⟨eI⟩⟩ := fstd_smallConcl h hL hchev hB hBc hidm hCB hdB hdL hK hs
  have hKL : K ≤ L := hK.1.trans inf_le_left
  rcases hs with hU | hA
  · have h2 := fstd_card_center_dvd_two hK.2.2 hU
    exact Nat.Coprime.coprime_dvd_right h2 (by norm_num)
  ·
    have h360 : Nat.card (↥((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ⧸
        Subgroup.center ↥((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))) =
          360 := by
      rw [Nat.card_congr eI.toEquiv]
      obtain ⟨e6⟩ := fstd_pSimple_equiv hK.2.2 (Or.inr hA)
      rw [← Nat.card_congr e6.toEquiv]
      exact fstd_card_of_isA6 hA
    obtain ⟨H, hIH, hHs, hH3⟩ := hA6 h360
    have hBN : B ≤ Subgroup.normalizer (L : Set X) := S11.le_normalizer_of_innerDiag hidm
    have hIqs := (fstd_image hL hBN hdB hK).1.2.2
    let π : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' _
    let K' : Subgroup ↥L := K.subgroupOf L
    have hHnc : ∃ a b : ↥H, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := fstd_exists_noncomm hIqs
      refine ⟨⟨a, hIH a.2⟩, ⟨b, hIH b.2⟩, fun h' => hab (Subtype.ext ?_)⟩
      have h'' := congrArg (fun w : ↥H => (w : ↥L ⧸ Subgroup.center ↥L)) h'
      exact h''
    obtain ⟨M, hM3, hMle⟩ := fstd_cover H hHs hHnc hH3
    have hK'qs : CFSG.Open.IsQuasisimple ↥K' :=
      hK.2.2.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL)
    have hK'M : K' ≤ M := hMle K' (Subgroup.isPerfect_iff.mp ⟨hK'qs.1⟩) hIH
    have hcenK : ∀ z ∈ K, (∀ k ∈ K, k * z = z * k) → ∀ l ∈ L, l * z = z * l :=
      fstd_mem_center_of_image hKL hZI
    let f : ↥(Subgroup.center ↥K') →* ↥(Subgroup.center ↥M) :=
      { toFun := fun z => ⟨⟨(z : ↥K'), hK'M (z : ↥K').2⟩, by
          rw [Subgroup.mem_center_iff]
          intro y
          apply Subtype.ext
          apply Subtype.ext
          have hzK : (((z : ↥K') : ↥L) : X) ∈ K := (z : ↥K').2
          have hzc : ∀ k ∈ K, k * (((z : ↥K') : ↥L) : X) = (((z : ↥K') : ↥L) : X) * k := by
            intro k hk
            have h1 := Subgroup.mem_center_iff.1 z.2 ⟨⟨k, hKL hk⟩, hk⟩
            exact congrArg (fun w : ↥K' => ((w : ↥L) : X)) h1
          exact hcenK _ hzK hzc _ ((y : ↥L).2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w : ↥(Subgroup.center ↥M) => ((w : ↥M) : ↥L)) hab
    have hdvd : Nat.card ↥(Subgroup.center ↥K') ∣ Nat.card ↥(Subgroup.center ↥M) :=
      Subgroup.card_dvd_of_injective f hf
    have hKK' : Nat.card ↥(Subgroup.center ↥K) = Nat.card ↥(Subgroup.center ↥K') :=
      Nat.card_congr (Subgroup.centerCongr (Subgroup.subgroupOfEquivOfLe hKL).symm).toEquiv
    rw [hKK']
    exact Nat.Coprime.coprime_dvd_right hdvd hM3

end Odd

end CFSG.LocalAnalysis.GLTheoremA.FStdDiag

end
