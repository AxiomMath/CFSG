module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporHull
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefLocal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113K.DetFF
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMOrder
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompSporHeRu
public import CFSG.LargeExtraspecial.OutSixBasic
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporOrder
public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.KStep
public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.NoSevenPrime
public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.Planes
public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.Pure
public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.Solvable

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporCent

open Subgroup
open CFSG.Sporadic.Fi24 CFSG.HardMathSupport.Dickson.I271.Fi7
open CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge SporadicOrdersTable)

theorem normalizer_zpowers_le_normalizer_of_sevenLine {G : Type*} [Group G] {p : ℕ} {c : G}
    {F : Subgroup G} (hL : CFSG.HardMathSupport.Dickson.I271.SevenLine p c F)
    (hFp : ∀ f ∈ F, ∃ n : ℕ, f ^ (p ^ n) = 1) :
    normalizer ((zpowers c : Subgroup G) : Set G) ≤ normalizer (F : Set G) := by
  have key : ∀ n ∈ normalizer ((zpowers c : Subgroup G) : Set G), ∀ f ∈ F, n * f * n⁻¹ ∈ F := by
    intro n hn f hf
    obtain ⟨m, hm⟩ := hFp f hf
    refine hL.syl _ ?_ ⟨m, by rw [conj_pow, hm]; group⟩
    rw [mem_centralizer_singleton_iff]
    have hc' : n⁻¹ * c * n ∈ zpowers c := by
      have h1 := (mem_normalizer_iff.mp (inv_mem hn) c).mp (mem_zpowers c)
      simpa using h1
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hc'
    have hfc : f * c = c * f := mem_centralizer_singleton_iff.mp (hL.le_cent hf)
    have hfck : f * c ^ k = c ^ k * f := (show Commute f c from hfc).zpow_right k
    calc n * f * n⁻¹ * c = n * (f * (n⁻¹ * c * n)) * n⁻¹ := by group
      _ = n * (f * c ^ k) * n⁻¹ := by rw [hk]
      _ = n * (c ^ k * f) * n⁻¹ := by rw [hfck]
      _ = (n * c ^ k * n⁻¹) * (n * f * n⁻¹) := by group
      _ = c * (n * f * n⁻¹) := by rw [hk]; group
  intro n hn
  rw [mem_normalizer_iff]
  intro f
  refine ⟨key n hn f, fun hf => ?_⟩
  have h1 := key n⁻¹ (inv_mem hn) _ hf
  simpa [mul_assoc] using h1

theorem exists_he_normal_fi24 (hb : LieOrderBridge) (hOrd : SporadicOrdersTable)
    {W Et : Subgroup J} (hWK : CFSG.Open.IsKGroup W)
    (hWtop : W ≠ ⊤) (hEtQ : Et ≤ Q7) (hEtc : Nat.card Et = 7 ^ 2)
    (hNQ : normalizer (Q7 : Set J) ≤ W)
    (hEtC : ∀ t ∈ Et, t ≠ 1 → centralizer ({t} : Set J) ≤ W) :
    ∃ H : Subgroup J, H ≤ W ∧ Nonempty (H ≃* (TauCeti.CFSGIndex.sporadic .He).Group) ∧
      (H.subgroupOf W).Normal ∧ centralizer (H : Set J) = ⊥ := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hcE, hcases⟩ := plane_cases hEtQ hEtc
  have hQ7p : ∀ f ∈ Q7, ∃ n : ℕ, f ^ (7 ^ n) = 1 := fun f hf => ⟨3, by
    have h := pow_card_eq_one' (G := Q7) (x := ⟨f, hf⟩)
    rw [card_Q7] at h
    simpa using congrArg Subtype.val h⟩
  have hNc : normalizer ((zpowers C7 : Subgroup J) : Set J) ≤ W :=
    (normalizer_zpowers_le_normalizer_of_sevenLine sevenLine_c hQ7p).trans hNQ
  have hYne : Y7 ≠ 1 := by
    intro h
    apply C7_ne_one
    calc C7 = X7 * Y7 * X7 ^ 6 * Y7 ^ 6 := fi7_cube.2.2.1
      _ = X7 * X7 ^ 6 := by rw [h]; simp
      _ = X7 ^ 7 := by rw [← pow_succ']
      _ = 1 := fi7_cube.1
  have hXne : X7 ≠ 1 := by
    intro h
    apply C7_ne_one
    calc C7 = X7 * Y7 * X7 ^ 6 * Y7 ^ 6 := fi7_cube.2.2.1
      _ = Y7 * Y7 ^ 6 := by rw [h]; simp
      _ = Y7 ^ 7 := by rw [← pow_succ']
      _ = 1 := fi7_cube.2.1
  obtain ⟨lam, h1, h6, hXlam⟩ : ∃ lam : ℕ, 1 ≤ lam ∧ lam ≤ 6 ∧ X7 * Y7 ^ lam ∈ Et := by
    rcases hcases with hY | ⟨lam, hlam7, hXlam⟩
    · exfalso
      apply hWtop
      refine top_le_iff.1 ?_
      rw [← closure_normalizer_union_centralizer_Y7]
      exact (closure_le W).2 (Set.union_subset hNc (hEtC Y7 hY hYne))
    · rcases Nat.eq_zero_or_pos lam with h0 | hpos
      · exfalso
        subst h0
        simp only [pow_zero, mul_one] at hXlam
        apply hWtop
        refine top_le_iff.1 ?_
        rw [← closure_normalizer_union_centralizer_X7]
        exact (closure_le W).2 (Set.union_subset hNc (hEtC X7 hXlam hXne))
      · exact ⟨lam, hpos, by omega, hXlam⟩
  have hwc : X7 * Y7 ^ lam ∉ zpowers C7 := by
    intro hmem
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hmem
    have h1' : C7 ^ (n % 7) = C7 ^ n := by
      have := zpow_mod_orderOf C7 n
      rwa [orderOf_C7, Nat.cast_ofNat] at this
    have hk0 : 0 ≤ n % 7 := Int.emod_nonneg n (by norm_num)
    obtain ⟨k, hkdef⟩ := Int.eq_ofNat_of_zero_le hk0
    have hk7 : k < 7 := by
      have hk7' : n % 7 < 7 := Int.emod_lt_of_pos n (by norm_num)
      omega
    have h2 : C7 ^ k = X7 * Y7 ^ lam := by
      rw [← hn, ← h1', hkdef, zpow_natCast]
    have h3 := fi7_cube.2.2.2.2.2 0 0 k 1 lam 0 (by norm_num) (by norm_num) hk7
      (by norm_num) (by omega) (by norm_num) (by simpa using h2)
    omega
  obtain ⟨H, hHcl, ⟨eH⟩, hQH, h, hhH, hhw⟩ := exists_he_le_closure (lam := lam) h1 h6
  have hHW : H ≤ W := hHcl.trans ((closure_le W).2 (Set.union_subset hNc
    (hEtC _ hXlam fun hne => hwc (hne ▸ one_mem _))))
  obtain ⟨bHe⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have eC : H ≃* CFSG.Blueprint.NativeSporadic.Carrier .He := eH.trans bHe.symm
  have hHs : IsSimpleGroup H :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He eC
  have hHc : Nat.card H = 4030387200 := (Nat.card_congr eC.toEquiv).trans CFSG.Sporadic.He.card_He
  have hwQ : X7 * Y7 ^ lam ∈ Q7 := Q7.mul_mem X7_mem (Q7.pow_mem Y7_mem lam)
  have hF1 : ∀ N : Subgroup J, ¬ 7 ∣ Nat.card N → H ≤ normalizer (N : Set J) → N = ⊥ :=
    fun N hN hHN => eq_bot_of_le_normalizer sevenLine_c hQH hwQ hwc hhH hhw hN hHN
  have hNs : IsSolvable (normalizer (Q7 : Set J)) := by
    have hsol : IsSolvable ↥(normalizer ((zpowers C7 : Subgroup J) : Set J)) :=
      isSolvable_normalizer_zpowers (G := J) sevenLine_c card_centralizer_C7
    exact @Group.isSolvable_of_isSolvable_injective _ _ _ _
      (inclusion (normalizer_le_normalizer_zpowers sevenLine_c)) (inclusion_injective _) hsol
  have hG : Nat.card J = 1255205709190661721292800 := card_J
  have h4H : 4 ∣ Nat.card H := by rw [hHc]; norm_num
  have hHnab : ∃ a b : H, a * b ≠ b * a :=
    @CFSG.AGLEmbedding.ThreeFives.exists_noncomm_of_simple H _ hHs h4H
  set L : Subgroup J :=
    (normalClosure ((H.subgroupOf W : Subgroup W) : Set W)).map W.subtype with hLdef
  have hHL : H ≤ L := fun x hx =>
    mem_map.mpr ⟨⟨x, hHW hx⟩, le_normalClosure (mem_subgroupOf.mpr hx), rfl⟩
  have hLW : L ≤ W := map_subtype_le _
  have hLs : IsSimpleGroup L := isSimpleGroup_normalClosure_map hHW hHs
    (by rw [hHc]; norm_num) (by rw [hG]; norm_num) (by rw [hG]; norm_num) hF1
  have hLnab : ∃ a b : L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hHnab
    exact ⟨⟨a, hHL a.2⟩, ⟨b, hHL b.2⟩, fun hh => hab (Subtype.ext (by
      simpa using congrArg (fun z : L => (z : J)) hh))⟩
  have hLp : ⁅L, L⁆ = L :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.commutator_eq_self_of_isSimpleGroup hLs hLnab
  have hLK : L.subgroupOf W = normalClosure ((H.subgroupOf W : Subgroup W) : Set W) :=
    comap_map_eq_self_of_injective W.subtype_injective _
  have hLn : (L.subgroupOf W).Normal := by
    rw [hLK]
    exact normalClosure_normal
  have hL1 : L ≠ ⊥ := by
    intro h0
    obtain ⟨a, b, hab⟩ := hHnab
    have ha : (a : J) = 1 := by
      have := hHL a.2
      rwa [h0, mem_bot] at this
    exact hab (by rw [show a = 1 from Subtype.ext ha, one_mul, mul_one])
  have hLH : L = H := eq_of_isKGroup_of_le hb hOrd hG hWK hWtop hHW hHs hHc hQH card_Q7 hF1 hNs
    hLW hL1 hLp (CFSG.Open.IsSubnormal.step hLW hLn (CFSG.Open.IsSubnormal.refl W))
  refine ⟨H, hHW, ⟨eH⟩, hLH ▸ hLn, ?_⟩
  set N : Subgroup J := centralizer (H : Set J) with hNdef
  have hHN : H ≤ normalizer (N : Set J) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    rw [hNdef, mem_centralizer_iff, mem_centralizer_iff]
    constructor
    · intro hy z hz
      have h1' := hy (x⁻¹ * z * x) (H.mul_mem (H.mul_mem (H.inv_mem hx) hz) hx)
      calc z * (x * y * x⁻¹) = x * ((x⁻¹ * z * x) * y) * x⁻¹ := by group
        _ = x * (y * (x⁻¹ * z * x)) * x⁻¹ := by rw [h1']
        _ = x * y * x⁻¹ * z := by group
    · intro hy z hz
      have h1' := hy (x * z * x⁻¹) (H.mul_mem (H.mul_mem hx hz) (H.inv_mem hx))
      calc z * y = x⁻¹ * ((x * z * x⁻¹) * (x * y * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * y * x⁻¹) * (x * z * x⁻¹)) * x := by rw [h1']
        _ = y * z := by group
  by_cases h7 : 7 ∣ Nat.card N
  ·
    exfalso
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := N) 7 h7
    have hu7 : orderOf (u : J) = 7 := by rw [Subgroup.orderOf_coe, hu]
    have hcomm : ∀ q ∈ H, q * (u : J) = (u : J) * q := fun q hq =>
      mem_centralizer_iff.mp u.2 q hq
    obtain ⟨S0, hS0⟩ := Q7_sylow
    have hQu : Q7 ≤ normalizer ((zpowers (u : J) : Subgroup J) : Set J) := by
      refine le_trans ?_ (CFSG.LocalAnalysis.RankThreeTheoremC.centralizer_singleton_le_normalizer_zpowers (u : J))
      intro q hq
      exact mem_centralizer_singleton_iff.mpr (hcomm q (hQH hq))
    have hPp : IsPGroup 7 (Q7 ⊔ zpowers (u : J) : Subgroup J) :=
      IsPGroup.to_sup_of_normal_right' (IsPGroup.of_card card_Q7)
        (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu7, pow_one])) hQu
    have hPeq : (Q7 ⊔ zpowers (u : J) : Subgroup J) = Q7 :=
      (S0.is_maximal' hPp (by rw [hS0]; exact le_sup_left)).trans hS0
    have huQ : (u : J) ∈ Q7 := by
      have h1' : (u : J) ∈ (Q7 ⊔ zpowers (u : J) : Subgroup J) := mem_sup_right (mem_zpowers _)
      rwa [hPeq] at h1'
    obtain ⟨a, b, hab⟩ := hHnab
    have hZH := CFSG.Sporadic.Schreier.center_eq_bot_of_simple hHs hab
    have hzc : (⟨u, hQH huQ⟩ : H) ∈ center H :=
      mem_center_iff.mpr fun g => Subtype.ext (hcomm g g.2)
    rw [hZH, mem_bot] at hzc
    have hu1 : (u : J) = 1 := congrArg Subtype.val hzc
    rw [hu1, orderOf_one] at hu7
    norm_num at hu7
  · exact hF1 N h7 hHN

end CFSG.LocalAnalysis.AGL81I.Section3.SporCent
namespace CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (oPrimeModPrimeComplement)
open CFSG.Sporadic.Fi24 CFSG.HardMathSupport.Dickson.I271.Fi7
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge SporadicOrdersTable)

theorem conclusion_of_fi24Prime (hb : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (hbr : CFSG.Quasithin.B113KDet.CatalogBridge)
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}
    (h : ThreeNineHyp K E D X₁ 7 d)
    (hs : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .Fi24Prime) :
    ThreeNineConclusion K D X₁ 7 d := by
  obtain ⟨e⟩ := hs
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hsK : IsSimpleGroup ↥K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi24.isSimpleGroup_Fi24prime e
  have hcK : Nat.card ↥K = 1255205709190661721292800 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Fi24.card_Fi24prime
  have hZ : Subgroup.center ↥K = ⊥ :=
    SporCent.center_eq_bot_of_not_prime (by rw [hcK]; norm_num)
  have hO : Nat.card (Outer ↥K) = 2 := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.Sporadic.Schreier.Fi24.card_outer_fi24prime
  have hdp := h.d_prime
  have hout7 : ¬ 7 ∣ Nat.card (Outer ↥K) := by rw [hO]; norm_num
  have houtd : ¬ d ∣ Nat.card (Outer ↥K) := fun hd => by
    rw [hO] at hd
    exact h.d_ne_two ((Nat.prime_dvd_prime_iff_eq hdp Nat.prime_two).1 hd)
  have hDK : D ≤ K := h.D_le_K_of_not_dvd hZ houtd
  have hX₁K : X₁ ≤ K := h.lt.le.trans (sup_le le_rfl hDK)
  obtain ⟨Ebar, -, hEc, hEC, hEN⟩ := h.exists_barE hZ hout7
  obtain ⟨S, hES⟩ := (IsPGroup.of_card hEc).exists_le_sylow
  let θ : ↥K ≃* ↥J := e.trans CFSG.Sporadic.Fi24.fi24EquivJ
  let θm : ↥K →* ↥J := θ
  obtain ⟨S0, hS0⟩ := Q7_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥J
    (Sylow.mapSurjective (f := θm) θ.surjective S) S0
  let γm : ↥J →* ↥J := (MulAut.conj g : ↥J →* ↥J)
  have hγapply : ∀ x : ↥J, γm x = g * x * g⁻¹ := fun x => MulAut.conj_apply g x
  have hγinj : Function.Injective γm := by
    intro x y hxy
    rw [hγapply, hγapply] at hxy
    simpa using hxy
  have hγsurj : Function.Surjective γm := fun y => ⟨g⁻¹ * y * g, by rw [hγapply]; group⟩
  let φm : ↥K →* ↥J := γm.comp θm
  have hφinj : Function.Injective φm := hγinj.comp θ.injective
  have hφsurj : Function.Surjective φm := hγsurj.comp θ.surjective
  have hSφ : (S : Subgroup ↥K).map φm = Q7 := by
    have h1 : ((S0 : Subgroup ↥J)) =
        ((S : Subgroup ↥K).map θm).map (MulAut.conj g : ↥J →* ↥J) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      rfl
    rw [← hS0, h1, Subgroup.map_map]
  set Et : Subgroup ↥J := Ebar.map φm with hEtdef
  have hEtQ : Et ≤ Q7 := by
    rw [← hSφ]
    exact Subgroup.map_mono hES
  have hEtc : Nat.card Et = 7 ^ 2 := by
    rw [hEtdef, Subgroup.card_map_of_injective hφinj, hEc]
  set W : Subgroup ↥J := (X₁.subgroupOf K).map φm with hWdef
  have hWc : Nat.card W = Nat.card (X₁.subgroupOf K) :=
    Subgroup.card_map_of_injective hφinj
  have hNQ : Subgroup.normalizer (Q7 : Set ↥J) ≤ W := by
    rw [← hSφ, ← Subgroup.map_normalizer_eq_of_bijective _ ⟨hφinj, hφsurj⟩]
    exact Subgroup.map_mono (hEN S S.isPGroup' hES)
  have hEtC : ∀ t ∈ Et, t ≠ 1 → Subgroup.centralizer ({t} : Set ↥J) ≤ W := by
    rintro _ ⟨v, hv, rfl⟩ ht x hx
    have hv1 : v ≠ 1 := fun h1 => ht (by rw [h1, map_one])
    obtain ⟨y, rfl⟩ := hφsurj x
    refine ⟨y, hEC v hv hv1 ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    apply hφinj
    rw [map_mul, map_mul]
    exact hx
  have hWtop : W ≠ ⊤ := by
    intro htop
    apply h.not_K_le
    intro x hx
    obtain ⟨k, hk, hkx⟩ : φm ⟨x, hx⟩ ∈ W := by rw [htop]; exact Subgroup.mem_top _
    have hk' : k = ⟨x, hx⟩ := hφinj hkx
    exact Subgroup.mem_subgroupOf.mp (hk' ▸ hk)
  have hWK : CFSG.Open.IsKGroup W := by
    have hK1 : CFSG.SectionRank.IsKGroupCat ↥W :=
      (h.kgroup.subgroup (X₁.subgroupOf K)).of_injective
        (((X₁.subgroupOf K).equivMapOfInjective φm hφinj).symm :
          ↥W →* ↥(X₁.subgroupOf K)) (MulEquiv.injective _)
    unfold CFSG.Open.IsKGroup
    unfold CFSG.SectionRank.IsKGroupCat at hK1
    intro A B _ _ hsAB _
    exact hbr _ (hK1 A (B.subgroupOf A) hsAB)
  obtain ⟨H, hHW, ⟨eH⟩, hHn, hCH⟩ :=
    SporCent.exists_he_normal_fi24 hb hOrd hWK hWtop hEtQ hEtc hNQ hEtC
  obtain ⟨bHe⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have eHW : ↥(H.subgroupOf W) ≃* CFSG.Blueprint.NativeSporadic.Carrier .He :=
    ((Subgroup.subgroupOfEquivOfLe hHW).trans eH).trans bHe.symm
  have : (H.subgroupOf W).Normal := hHn
  have hC : Subgroup.centralizer ((H.subgroupOf W : Subgroup W) : Set W) ≤ H.subgroupOf W := by
    intro w hw
    have hwJ : (w : ↥J) ∈ Subgroup.centralizer (H : Set ↥J) := by
      rw [Subgroup.mem_centralizer_iff] at hw ⊢
      intro x hx
      have h1 := congrArg Subtype.val (hw ⟨x, hHW hx⟩ (Subgroup.mem_subgroupOf.mpr hx))
      rwa [Subgroup.coe_mul, Subgroup.coe_mul] at h1
    rw [hCH, Subgroup.mem_bot] at hwJ
    rw [show w = 1 from Subtype.ext hwJ]
    exact Subgroup.one_mem _
  have hidx : (H.subgroupOf W).index ∣ 2 := by
    have h2 := CFSG.LargeExtraspecial.S14.index_dvd_card_outer_of_mulEquiv (H.subgroupOf W) hC
      (eHW.trans CFSG.Sporadic.HeldB.heEquivP)
    rwa [CFSG.Quasithin.H13.S126C.card_outer_heP] at h2
  have hHc : Nat.card (H.subgroupOf W) = 4030387200 :=
    (Nat.card_congr eHW.toEquiv).trans CFSG.Sporadic.He.card_He
  have hWcard : Nat.card W = 4030387200 * (H.subgroupOf W).index := by
    rw [← hHc]
    exact ((H.subgroupOf W).card_mul_index).symm
  have hidx12 : (H.subgroupOf W).index = 1 ∨ (H.subgroupOf W).index = 2 := by
    have hle := Nat.le_of_dvd (by norm_num) hidx
    have hpos : 0 < (H.subgroupOf W).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    omega
  obtain ⟨hd1, hd2⟩ := h.dvd_card_of_subgroupOf_le hDK le_rfl
  rw [← hWc] at hd1 hd2
  have hWdvd : Nat.card W ∣ 2 ^ 11 * (3 ^ 3 * (5 ^ 2 * (7 ^ 3 * 17))) := by
    rw [hWcard]
    rcases hidx12 with h1 | h1 <;> rw [h1] <;> norm_num
  have hXidx : (X₁.subgroupOf K).index = 311435513985024 ∨
      (X₁.subgroupOf K).index = 155717756992512 := by
    have h1 := (X₁.subgroupOf K).card_mul_index
    rw [← hWc, hWcard, hcK] at h1
    rcases hidx12 with h2 | h2 <;> rw [h2] at h1
    · left; omega
    · right; omega
  have hd17 : d = 17 := by
    have h' := hd1.trans hWdvd
    rcases hdp.dvd_mul.1 h' with h2 | h'
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hdp Nat.prime_two).1 (hdp.dvd_of_dvd_pow h2))
        h.d_ne_two
    rcases hdp.dvd_mul.1 h' with h3 | h'
    ·
      have h3' := (Nat.prime_dvd_prime_iff_eq hdp Nat.prime_three).1 (hdp.dvd_of_dvd_pow h3)
      subst h3'
      rw [hcK, SporCent.factorization_eq_of_pow_dvd (e := 16) Nat.prime_three (by norm_num)
        (by norm_num) (by norm_num)] at hd2
      exact absurd (hd2.trans hWdvd) (by norm_num)
    rcases hdp.dvd_mul.1 h' with h5 | h'
    ·
      have h5' := (Nat.prime_dvd_prime_iff_eq hdp Nat.prime_five).1 (hdp.dvd_of_dvd_pow h5)
      subst h5'
      have hmod := (h.isBorelDLocal hZ hout7).index_modEq_one_of_dvd hdp
        (by rw [hcK]; norm_num)
      rcases hXidx with hi | hi <;> rw [hi] at hmod <;> exact absurd hmod (by decide)
    rcases hdp.dvd_mul.1 h' with h7 | h17
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hdp Nat.prime_seven).1 (hdp.dvd_of_dvd_pow h7))
        h.d_ne
    · exact (Nat.prime_dvd_prime_iff_eq hdp (by norm_num)).1 h17
  subst hd17
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have hDc : Nat.card D = 17 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_D
    have hdvd : 17 ^ k ∣ 1255205709190661721292800 := hk ▸ hcK ▸ Subgroup.card_dvd_of_le hDK
    have hk1 : k ≤ 1 := by
      by_contra hk2
      exact absurd ((pow_dvd_pow 17 (by omega : 2 ≤ k)).trans hdvd) (by norm_num)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact h.D_ne_bot (Subgroup.eq_bot_of_card_eq D (by rw [hk, pow_zero]))
    rw [hk, show k = 1 by omega, pow_one]
  refine ⟨isCyclic_of_prime_card hDc, hDK,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, ⟨e⟩, ?_⟩)))))⟩
  have : IsSimpleGroup ↥(H.subgroupOf W) :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He eHW
  obtain ⟨e1⟩ := SporCent.nonempty_oPrimeModPrimeComplement_mulEquiv (G := ↥J) (d := 17)
    (by norm_num) (Y := W) (H.subgroupOf W) (by rw [hHc]; norm_num)
    (fun h17 => by
      have := Nat.le_of_dvd (by norm_num) (h17.trans hidx)
      omega)
  have e2 : ↥X₁ ≃* ↥W := (Subgroup.subgroupOfEquivOfLe hX₁K).symm.trans
    ((X₁.subgroupOf K).equivMapOfInjective φm hφinj)
  obtain ⟨e3⟩ := oPrimeModPrimeComplement_congr 17 e2
  exact ⟨(e3.trans e1).trans eHW⟩

end CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp
