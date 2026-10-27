module

public import CFSG.HardMathSupport.Dickson.BMRows.KFormDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS05I1416Arith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416QFinal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416TConv

public section

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Blueprint
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped commutatorElement

theorem isKGroup_pSimple {G : Type} [Group G] {p : ℕ} {X K : Subgroup G}
    (hX : CFSG.Open.IsKGroup ↥X) (hK : GLAPComponent p X K) :
    CFSG.Open.IsKGroup (PSimple p K) :=
  ((hX.of_le hK.1).quotient _).quotient _

private theorem kf_catalogIs_congr {S T : Type} [Group S] [Group T] (e : S ≃* T)
    {Q : TauCeti.CFSGIndex → Prop} : catalogIs S Q ↔ catalogIs T Q :=
  ⟨fun ⟨i, hi, ⟨f⟩⟩ => ⟨i, hi, ⟨e.symm.trans f⟩⟩, fun ⟨i, hi, ⟨f⟩⟩ => ⟨i, hi, ⟨e.trans f⟩⟩⟩

private theorem kf_char_prime (d : TauCeti.LieTypeIndex) : d.characteristic.Prime := by
  cases d <;> simp <;>
    first | exact ‹TauCeti.PrimePower›.prime_p | exact Nat.prime_two | exact Nat.prime_three

section KRows


theorem isKGroup_carrier_of_mulEquiv {T : Type} [Group T] (hT : CFSG.Open.IsKGroup T)
    {s : TauCeti.SporadicName} (e : T ≃* (TauCeti.CFSGIndex.sporadic s).Group) :
    CFSG.Open.IsKGroup (NativeSporadic.Carrier s) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  exact hT.of_surjective (e.trans b.symm).toMonoidHom (e.trans b.symm).surjective

theorem kRows_of_isKGroup {T : Type} [Group T] (hT : CFSG.Open.IsKGroup T)
    {s : TauCeti.SporadicName} (e : T ≃* (TauCeti.CFSGIndex.sporadic s).Group) :
    (s = .B → CFSG.Open.IsKGroup (NativeSporadic.Carrier .B)) ∧
      (s = .M → CFSG.Open.IsKGroup (NativeSporadic.Carrier .M)) := by
  have h := isKGroup_carrier_of_mulEquiv hT e
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · subst hs
    exact h
  · subst hs
    exact h

end KRows

section QSpor

open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.PerfectAutomorphisms

private theorem kf_exists_conjAut {Q : Type} [Group Q] {K : Subgroup Q} {y : Q}
    (hyN : y ∈ Subgroup.normalizer (K : Set Q)) {n : ℕ} (hy : y ^ n = 1) :
    ∃ β : MulAut ↥K, β ^ n = 1 ∧
      fixSubgroup β = (K ⊓ Subgroup.centralizer ({y} : Set Q)).subgroupOf K := by
  obtain ⟨β, hβdef⟩ : ∃ β : MulAut ↥K, β = Subgroup.normalizerMonoidHom K ⟨y, hyN⟩ :=
    ⟨_, rfl⟩
  have hβapp : ∀ k : ↥K, ((β k : ↥K) : Q) = y * (k : Q) * y⁻¹ := by
    intro k
    rw [hβdef]
    rfl
  refine ⟨β, ?_, ?_⟩
  · have h3 : (⟨y, hyN⟩ : Subgroup.normalizer (K : Set Q)) ^ n = 1 := Subtype.ext hy
    rw [hβdef, ← map_pow, h3, map_one]
  · ext k
    rw [mem_fixSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hk
      have h1 : ((β k : ↥K) : Q) = (k : Q) := congrArg Subtype.val hk
      rw [hβapp] at h1
      exact ⟨k.2, (mul_inv_eq_iff_eq_mul.1 h1).symm⟩
    · rintro ⟨-, hk⟩
      apply Subtype.ext
      rw [hβapp]
      exact mul_inv_eq_iff_eq_mul.2 hk.symm


theorem i1416Spor_of_SK (h : I1416QSporSK) {G : Type} [Group G] [Finite G] {p : ℕ}
    {X K J : Subgroup G} {y : G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : GLAPComponent p X K)
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) (hyp : y ^ p = 1) (hncent : ¬ CentMod p K y)
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J)
    (s : TauCeti.SporadicName) (e : PSimple p K ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hB : s = .B → CFSG.Open.IsKGroup (NativeSporadic.Carrier .B))
    (hM : s = .M → CFSG.Open.IsKGroup (NativeSporadic.Carrier .M))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hJchev : IsChevSimple q (PSimple p J))
    (hA : ∃ A : Subgroup (MulAut (PSimple p J)), IsElemAbelian p A ∧ p ^ 2 ≤ Nat.card A) :
    False := by
  have hyp' : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hyp
  obtain ⟨Q, _, _, K', y', ⟨eK⟩, hnorm, hpow, hcentmod, hcomp⟩ :=
    exists_pQuot_transfer hp hyp' hyN
  obtain ⟨J₁, hJ₁, ⟨eJ⟩⟩ := hcomp J hJ
  have hJ₁le : J₁ ≤ K' := hJ₁.1.trans inf_le_left
  have hq0 : CFSG.Open.IsQuasisimple (PQuot p K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  have hq' : CFSG.Open.IsQuasisimple ↥K' :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eK.symm hq0
  haveI : Group.IsPerfect ↥K' := ⟨hq'.1⟩
  have eS : (↥K' ⧸ Subgroup.center ↥K') ≃* PSimple p K :=
    QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)
  obtain ⟨β, hβp, hβfix⟩ := kf_exists_conjAut hnorm (hpow p hyp)
  have hJ₁' : GLAPComponent p (fixSubgroup β) (J₁.subgroupOf K') := by
    rw [hβfix]
    exact glaPComponent_subgroupOf hp inf_le_left hJ₁
  have hker : (QuotientGroup.mk' (Subgroup.center ↥K')).ker ≤ Subgroup.center ↥K' :=
    (QuotientGroup.ker_mk' _).le
  have hπs : Function.Surjective (QuotientGroup.mk' (Subgroup.center ↥K')) :=
    QuotientGroup.mk'_surjective _
  have hαβ : ∀ k : ↥K', QuotientGroup.mk' (Subgroup.center ↥K') (β k) =
      centerQuotientHom ↥K' β (QuotientGroup.mk' (Subgroup.center ↥K') k) :=
    fun k => (onCenterQuotient_apply_mk β k).symm
  have hJS0 : GLAPComponent p (fixSubgroup (centerQuotientHom ↥K' β))
      ((J₁.subgroupOf K').map (QuotientGroup.mk' (Subgroup.center ↥K'))) :=
    glaPComponent_map_fixSubgroup (QuotientGroup.mk' (Subgroup.center ↥K')) hker β
      (centerQuotientHom ↥K' β) hαβ hπs hp hJ₁'
  have hβbarP : (centerQuotientHom ↥K' β) ^ p = 1 := by rw [← map_pow, hβp, map_one]
  have hβbar1 : centerQuotientHom ↥K' β ≠ 1 := by
    intro hb
    have hβ1 : β = 1 := centerQuotientHom_injective ↥K' (hb.trans (map_one _).symm)
    apply hncent
    apply hcentmod
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥K') ∈ fixSubgroup β := by
      rw [mem_fixSubgroup, hβ1]
      rfl
    rw [hβfix, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hmem
    exact hmem.2
  have g₁ : PQuot p (J₁.subgroupOf K') ≃* PQuot p J₁ :=
    (nonempty_pQuot_equiv_subgroupOf p hJ₁le).some
  have g : PQuot p (J₁.subgroupOf K') ≃* PQuot p J := g₁.trans eJ.symm
  have fJ : PSimple p (J₁.subgroupOf K') ≃* PSimple p J :=
    QuotientGroup.congr _ _ g (Subgroup.map_center_eq g)
  obtain ⟨fS⟩ :=
    nonempty_pSimple_equiv_map hp (QuotientGroup.mk' (Subgroup.center ↥K')) hJ₁' hJS0
  obtain ⟨JS, hJSdef⟩ : ∃ JS : Subgroup (↥K' ⧸ Subgroup.center ↥K'),
      JS = (J₁.subgroupOf K').map (QuotientGroup.mk' (Subgroup.center ↥K')) := ⟨_, rfl⟩
  rw [← hJSdef] at hJS0 fS
  have eJS : PSimple p J ≃* PSimple p JS := fJ.symm.trans fS
  have hJSchev : IsChevSimple q (PSimple p JS) := chev_isChevSimple_of_mulEquiv eJS.symm hJchev
  have hJSA := i1416_elemAb_transfer eJS hA
  exact h (↥K' ⧸ Subgroup.center ↥K') s ⟨eS.trans e⟩ hB hM p hp hp2 (centerQuotientHom ↥K' β)
    hβbarP hβbar1 JS hJS0 q hq hq2 hqp hJSchev hJSA

end QSpor

section QMain


theorem i1416At_of_sporK (h : I1416QSporSK) (G : Type) [Group G] [Finite G] (p : ℕ) :
    I1416At G p := by
  intro hp hp2 q hq hq2 hqp X K J y hX hK hyN hyp hncent hJ hJchev hA
  have hAut : p ^ 2 ∣ Nat.card (MulAut (PSimple p J)) := i1416_sq_dvd_of_elemAb hp hA
  have hcat : IsCatalogGroup (PSimple p K) :=
    CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient'
      ((hX.of_le hK.1).quotient _) (isQuasisimple_pQuot_of_glaPComponent hp hK)
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic r hr =>
    exfalso
    obtain ⟨a, b, hab⟩ := (chev_pSimple_simple_nonabelian hp hK).2
    apply hab
    apply e.injective
    simp only [map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    exfalso
    obtain ⟨m, hm5, ⟨eJ⟩⟩ := i1416AltSmall hp hp2 hK hyN hyp hncent hJ hn e
    exact i1416AltArith hm5 eJ hp hp2 hq hq2 hqp hJchev hAut
  | sporadic s =>
    obtain ⟨hB, hM⟩ := kRows_of_isKGroup (isKGroup_pSimple hX hK) e
    exact (i1416Spor_of_SK h hp hp2 hK hyN hyp hncent hJ s e hB hM hq hq2 hqp hJchev hA).elim
  | lie d =>
    by_cases hd : d.1.characteristic = q
    · exact Or.inl ⟨TauCeti.CFSGIndex.lie d, by simpa [onLie] using hd, ⟨e⟩⟩
    · exfalso
      have hr : d.1.characteristic.Prime := kf_char_prime d.1
      have hKr : IsChevSimple d.1.characteristic (PSimple p K) :=
        Or.inl ⟨TauCeti.CFSGIndex.lie d, by simp [onLie], ⟨e⟩⟩
      have hyN' : Subgroup.zpowers y ≤ Subgroup.normalizer (K : Set G) :=
        Subgroup.zpowers_le.2 hyN
      have hyp' : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hyp
      have hA' : IsElemAbelian p (Subgroup.zpowers y) := by
        refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
        · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
          obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
          apply Subtype.ext
          show (a : G) * b = b * a
          rw [← hm, ← hn]
          exact (Commute.refl y).zpow_zpow m n |>.eq
        · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx
          rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyp, one_zpow]
      have hcen : Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) =
          Subgroup.centralizer ({y} : Set G) := by
        ext g
        simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff,
          forall_eq]
        constructor
        · intro h
          exact h y (Subgroup.mem_zpowers y)
        · intro h z hz
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
          exact (Commute.zpow_left (show Commute y g from h) m).eq
      have hJr : IsChevSimple d.1.characteristic (PSimple p J) :=
        (chevClosureQAt_of_lieComp_lieComps (G := G) lieComp_holds
          (fun _ hq' h5 => lieCompsOn_holds hq' h5) hp hp2)
          hp hp2 d.1.characteristic hr X K (Subgroup.zpowers y) hX hK hKr hA' hyN'
          J (by rw [hcen]; exact hJ)
      exact i1416LieArith hp hp2 hq hq2 hqp hd hJr hJchev hAut

end QMain

section TwoSpor

open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.PerfectAutomorphisms


theorem i1416TwoSpor_of_SK (h : I1416TwoSporSK) (G : Type) [Group G] [Finite G] :
    I1416TwoSpor G := by
  intro p X J K A y hp hp2 hX hJ hyN hyp hncent hK hKchev hA hinn hcard hcat
  have hyp' : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hyp
  have hAut : p ^ 2 ∣ Nat.card (MulAut (PSimple p K)) := small_sq_dvd_aut hp hK hinn.1 hA hcard
  obtain ⟨Q, _, _, K', y', ⟨eJ⟩, hnorm, hpow, hcentmod, hcomp⟩ :=
    exists_pQuot_transfer hp hyp' hyN
  obtain ⟨K₁, hK₁, ⟨eK⟩⟩ := hcomp K hK
  have hK₁le : K₁ ≤ K' := hK₁.1.trans inf_le_left
  have hq : CFSG.Open.IsQuasisimple (PQuot p J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hq' : CFSG.Open.IsQuasisimple ↥K' :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eJ.symm hq
  haveI : Group.IsPerfect ↥K' := ⟨hq'.1⟩
  have eS : (↥K' ⧸ Subgroup.center ↥K') ≃* PSimple p J :=
    QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)
  obtain ⟨i, ⟨s, rfl⟩, ⟨e⟩⟩ := hcat
  obtain ⟨β, hβp, hβfix⟩ := kf_exists_conjAut hnorm (hpow p hyp)
  have hK₁' : GLAPComponent p (fixSubgroup β) (K₁.subgroupOf K') := by
    rw [hβfix]
    exact glaPComponent_subgroupOf hp inf_le_left hK₁
  have hker : (QuotientGroup.mk' (Subgroup.center ↥K')).ker ≤ Subgroup.center ↥K' :=
    (QuotientGroup.ker_mk' _).le
  have hπs : Function.Surjective (QuotientGroup.mk' (Subgroup.center ↥K')) :=
    QuotientGroup.mk'_surjective _
  have hαβ : ∀ k : ↥K', QuotientGroup.mk' (Subgroup.center ↥K') (β k) =
      centerQuotientHom ↥K' β (QuotientGroup.mk' (Subgroup.center ↥K') k) :=
    fun k => (onCenterQuotient_apply_mk β k).symm
  have hKS0 : GLAPComponent p (fixSubgroup (centerQuotientHom ↥K' β))
      ((K₁.subgroupOf K').map (QuotientGroup.mk' (Subgroup.center ↥K'))) :=
    glaPComponent_map_fixSubgroup (QuotientGroup.mk' (Subgroup.center ↥K')) hker β
      (centerQuotientHom ↥K' β) hαβ hπs hp hK₁'
  have hβbarP : (centerQuotientHom ↥K' β) ^ p = 1 := by rw [← map_pow, hβp, map_one]
  have hβbar1 : centerQuotientHom ↥K' β ≠ 1 := by
    intro hb
    have hβ1 : β = 1 := centerQuotientHom_injective ↥K' (hb.trans (map_one _).symm)
    apply hncent
    apply hcentmod
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥K') ∈ fixSubgroup β := by
      rw [mem_fixSubgroup, hβ1]
      rfl
    rw [hβfix, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hmem
    exact hmem.2
  have g₁ : PQuot p (K₁.subgroupOf K') ≃* PQuot p K₁ :=
    (nonempty_pQuot_equiv_subgroupOf p hK₁le).some
  have g : PQuot p (K₁.subgroupOf K') ≃* PQuot p K := g₁.trans eK.symm
  have fK : PSimple p (K₁.subgroupOf K') ≃* PSimple p K :=
    QuotientGroup.congr _ _ g (Subgroup.map_center_eq g)
  obtain ⟨fS⟩ :=
    nonempty_pSimple_equiv_map hp (QuotientGroup.mk' (Subgroup.center ↥K')) hK₁' hKS0
  obtain ⟨KS, hKSdef⟩ : ∃ KS : Subgroup (↥K' ⧸ Subgroup.center ↥K'),
      KS = (K₁.subgroupOf K').map (QuotientGroup.mk' (Subgroup.center ↥K')) := ⟨_, rfl⟩
  rw [← hKSdef] at hKS0 fS
  have eKS : PSimple p K ≃* PSimple p KS := fK.symm.trans fS
  have hKSchev : IsChevSimple 2 (PSimple p KS) := chev_isChevSimple_of_mulEquiv eKS.symm hKchev
  have hcardMA : Nat.card (MulAut (PSimple p KS)) = Nat.card (MulAut (PSimple p K)) :=
    Nat.card_congr (MulAut.congr eKS.symm).toEquiv
  have hL2S : ¬ (p = 3 ∧
      CFSG.HardMathSupport.Timmesfeld.ComponentBalance.IsL2TwoPowOdd (PSimple p KS)) := by
    rintro ⟨rfl, n, hn, hn1, ⟨eL⟩⟩
    obtain ⟨hs, hnc⟩ := chev_pSimple_simple_nonabelian hp hK
    haveI := hs
    exact i112d_l2_false hK hA hinn hcard (chev_center_eq_bot_of_simple_nonabelian hnc)
      ⟨n, hn, hn1, ⟨eKS.trans eL⟩⟩
  obtain ⟨hB, hM⟩ := kRows_of_isKGroup (isKGroup_pSimple hX hJ) e
  obtain ⟨hp3, hc⟩ := h (↥K' ⧸ Subgroup.center ↥K') s ⟨eS.trans e⟩ hB hM p hp hp2
    (centerQuotientHom ↥K' β) hβbarP hβbar1 KS hKS0 hKSchev (by rw [hcardMA]; exact hAut) hL2S
  subst hp3
  exact ⟨rfl, (kf_catalogIs_congr eKS.symm).1 hc⟩

end TwoSpor

section TwoAt


theorem i1416TwoAt_of_sporSK (h : I1416TwoSporSK) (G : Type) [Group G] [Finite G] :
    I1416TwoAt G :=
  i1416TwoAt_holds' G (i1416TwoSpor_of_SK h G)

end TwoAt

section Chev2


theorem i1416Chev2At_of_sporList_coreK (h : I1416Chev2SporListK) (G : Type) [Group G]
    [Finite G] (hB : Chev2BridgeAt G) (hQ : Chev2SporRank) (hO : Chev2OddAmb)
    (hClo : ∀ p : ℕ, p.Prime → p ≠ 2 → ChevClosureQAt G p) : I1416Chev2At G := by
  intro p p' X K J y hp hp2 hp' _hp'2 _hpp' hX hK' hK hyN hyp hJ hJchev hJq hJodd h6
  obtain ⟨e⟩ := pSimple_equiv_of_comps hp hp' hK' hK
  suffices hmain : IsChevSimple 2 (PSimple p K) from chev_isChevSimple_of_mulEquiv e hmain
  have hrank : catalogIs (PSimple p J) chev2Spor → False := by
    intro hsm
    obtain ⟨eq⟩ := chev2_quot_equiv hp hJ hJq
    exact absurd h6 (not_le.2 (hQ ↥J hJq hJodd ((kf_catalogIs_congr eq).2 hsm)))
  have hyp' : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hyp
  have hJch : IsChevSimple 2 (PSimple p J) :=
    hB p (K ⊓ Subgroup.centralizer ({y} : Set G)) J hp hJ hJchev
  by_cases hα1 : chevAut p K ⟨y, hyN⟩ = 1
  ·
    have hCM : CentMod p K y := (chevAut_eq_one_iff hp hK hyN).1 hα1
    obtain ⟨eJ⟩ := pQuot_equiv_of_centMod (X := X) hp hK hyp' hCM hJ
    have eS : PSimple p J ≃* PSimple p K :=
      QuotientGroup.congr (Subgroup.center (PQuot p J)) (Subgroup.center (PQuot p K)) eJ
        (Subgroup.map_center_eq eJ)
    exact chev_isChevSimple_of_mulEquiv eS.symm hJch
  ·
    have hαp : chevAut p K ⟨y, hyN⟩ ^ p = 1 := chevAut_pow_eq_one p K hyN hyp
    have hL : GLAPComponent p (fixSubgroup (chevAut p K ⟨y, hyN⟩)) (chevTransfer p K J) :=
      glaPComponent_chevTransfer hp hyN hyp' hJ
    obtain ⟨eJL⟩ := nonempty_pSimple_equiv_chevTransfer hp hyN hyp' hJ
    have hLch : IsChevSimple 2 (PSimple p (chevTransfer p K J)) :=
      chev_isChevSimple_of_mulEquiv eJL.symm hJch
    have hcat : IsCatalogGroup (PSimple p K) :=
      CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient'
        ((hX.of_le hK.1).quotient _) (isQuasisimple_pQuot_of_glaPComponent hp hK)
    obtain ⟨i, ⟨eT⟩⟩ := hcat
    cases i with
    | cyclic r hr =>
      exfalso
      obtain ⟨-, a, b, hab⟩ := chev_pSimple_simple_nonabelian hp hK
      apply hab
      apply eT.injective
      simp only [map_mul]
      exact mul_comm _ _
    | alternating n hn =>
      have hβ : (MulAut.congr eT) (chevAut p K ⟨y, hyN⟩) ^ p = 1 := by
        rw [← map_pow, hαp, map_one]
      have hβ1 : (MulAut.congr eT) (chevAut p K ⟨y, hyN⟩) ≠ 1 := fun h' =>
        hα1 ((MulAut.congr eT).injective (h'.trans (map_one _).symm))
      obtain ⟨hLe, ⟨eLe⟩⟩ := chevQ_transport hp eT hL
      obtain ⟨m, hm, -, ⟨f⟩⟩ := kdAltDown_holds n p hn hp hp2 _ hβ hβ1 _ hLe
      have hm5 : 5 ≤ m := (le_max_left 5 p).trans hm
      have hJA : PSimple p J ≃* alternatingGroup (Fin m) := eJL.trans (eLe.trans f)
      have hJ568 : m = 5 ∨ m = 6 ∨ m = 8 := by
        by_contra hne
        exact not_chev2_alt hm5 (by omega) hJA hJch
      have hsmall : catalogIs (PSimple p J) chev2Small :=
        ⟨TauCeti.CFSGIndex.alternating m hm5, hJ568, ⟨hJA⟩⟩
      exact (hrank (catalogIs_chev2Spor_of_small hsmall)).elim
    | sporadic s =>
      obtain ⟨hKB, hKM⟩ := kRows_of_isKGroup (isKGroup_pSimple hX hK) eT
      have hsm : catalogIs (PSimple p (chevTransfer p K J)) chev2Spor :=
        h (PSimple p K) s ⟨eT⟩ hKB hKM p hp hp2 (chevAut p K ⟨y, hyN⟩) hαp hα1
          (chevTransfer p K J) hL hLch
      have hJsm : catalogIs (PSimple p J) chev2Spor := (kf_catalogIs_congr eJL).2 hsm
      exact (hrank hJsm).elim
    | lie d =>
      by_cases h2 : d.1.characteristic = 2
      · exact Or.inl ⟨TauCeti.CFSGIndex.lie d, by simpa [onLie] using h2, ⟨eT⟩⟩
      ·
        have hr : d.1.characteristic.Prime := kf_char_prime d.1
        have hKr : IsChevSimple d.1.characteristic (PSimple p K) :=
          Or.inl ⟨TauCeti.CFSGIndex.lie d, by simp [onLie], ⟨eT⟩⟩
        have hyN' : Subgroup.zpowers y ≤ Subgroup.normalizer (K : Set G) :=
          Subgroup.zpowers_le.2 hyN
        have hA' : IsElemAbelian p (Subgroup.zpowers y) := by
          refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
          · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
            obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
            apply Subtype.ext
            show (a : G) * b = b * a
            rw [← hm, ← hn]
            exact (Commute.refl y).zpow_zpow m n |>.eq
          · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx
            rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyp,
              one_zpow]
        have hcen : Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) =
            Subgroup.centralizer ({y} : Set G) := by
          ext g
          simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff,
            forall_eq]
          constructor
          · intro hg
            exact hg y (Subgroup.mem_zpowers y)
          · intro hg z hz
            obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
            exact (Commute.zpow_left (show Commute y g from hg) m).eq
        have hJr : IsChevSimple d.1.characteristic (PSimple p J) :=
          hClo p hp hp2 hp hp2 d.1.characteristic hr X K (Subgroup.zpowers y) hX hK hKr hA' hyN'
            J (by rw [hcen]; exact hJ)
        have hsm := hO d.1.characteristic (PSimple p J) hr h2 hJch hJr
        exact (hrank (catalogIs_chev2Spor_of_small hsm)).elim

theorem i1416Chev2At_of_sporListK (h : I1416Chev2SporListK) (G : Type) [Group G] [Finite G]
    (hQ : Chev2SporRank) (hC : Chev2MarkedConverse) : I1416Chev2At G :=
  i1416Chev2At_of_sporList_coreK h G (chev2Bridge_of_marked hC G) hQ chev2OddAmb_holds
    (fun _ hp hp2 => chevClosureQAt_of_lieComp_lieComps (G := G) lieComp_holds
      (fun _ hq h5 => lieCompsOn_holds hq h5) hp hp2)

theorem i1416Chev2At_of_list_of_rankK (h : I1416Chev2SporListK) (hQ : Chev2SporRank)
    (G : Type) [Group G] [Finite G] : I1416Chev2At G :=
  i1416Chev2At_of_sporListK h G hQ chev2MarkedConverse_holds

end Chev2

section Chev2List


theorem i1416Chev2At_of_listK (h : I1416Chev2SporListK) (G : Type) [Group G] [Finite G] :
    I1416Chev2At G :=
  i1416Chev2At_of_list_of_rankK h chev2SporRank_holds G

end Chev2List

end CFSG.HardMathSupport.Dickson.BMRows
