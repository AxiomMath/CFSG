module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSocleCore
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporFi24

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

open CFSG.LocalAnalysis.RankThreeUC.AGL81C (oPPrimeHull)
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge SporadicOrdersTable)
open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Fi24 CFSG.HardMathSupport.Dickson.I271.Fi7

theorem exists_he_normal_of_fi24Prime (hb : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (hbr : CFSG.Quasithin.B113KDet.CatalogBridge)
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X}
    (h : ThreeNineHyp K E D X₁ 7 17)
    (hs : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .Fi24Prime) (hDK : D ≤ K) :
    ∃ T₀ : Subgroup X, T₀ ≤ X₁ ∧ (T₀.subgroupOf X₁).Normal ∧ IsSimpleGroup ↥T₀ ∧
      Nat.card ↥T₀ = 4030387200 ∧ (T₀.subgroupOf X₁).index ∣ 2 ∧
      Subgroup.centralizer (T₀ : Set X) ⊓ K = ⊥ := by
  obtain ⟨e⟩ := hs
  have : IsSimpleGroup ↥K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi24.isSimpleGroup_Fi24prime e
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hcK : Nat.card ↥K = 1255205709190661721292800 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Fi24.card_Fi24prime
  have hZ : Subgroup.center ↥K = ⊥ :=
    SporCent.center_eq_bot_of_not_prime (by rw [hcK]; norm_num)
  have hO : Nat.card (Outer ↥K) = 2 := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.Sporadic.Schreier.Fi24.card_outer_fi24prime
  have hout7 : ¬ 7 ∣ Nat.card (Outer ↥K) := by rw [hO]; norm_num
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
  let ψ : ↥X₁ →* ↥W :=
    { toFun := fun z => ⟨φm ⟨(z : X), hX₁K z.2⟩,
        Subgroup.mem_map_of_mem φm (Subgroup.mem_subgroupOf.mpr z.2)⟩
      map_one' := by
        apply Subtype.ext
        change φm (1 : ↥K) = 1
        exact map_one φm
      map_mul' := by
        intro x y
        apply Subtype.ext
        simpa [Subgroup.coe_mul] using
          map_mul φm ⟨(x : X), hX₁K x.2⟩ ⟨(y : X), hX₁K y.2⟩ }
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : (ψ x : ↥J) = (ψ y : ↥J) := congrArg Subtype.val hxy
    have h2 := hφinj h1
    exact Subtype.ext (congrArg (fun z : ↥K => (z : X)) h2)
  have hψsurj : Function.Surjective ψ := by
    intro w
    have hw : (w : ↥J) ∈ (X₁.subgroupOf K).map φm := hWdef ▸ w.2
    obtain ⟨k, hk, hkw⟩ := Subgroup.mem_map.mp hw
    refine ⟨⟨(k : X), Subgroup.mem_subgroupOf.mp hk⟩, ?_⟩
    apply Subtype.ext
    change φm ⟨(k : X), hX₁K (Subgroup.mem_subgroupOf.mp hk)⟩ = (w : ↥J)
    simpa using hkw
  have hψbij : Function.Bijective ψ := ⟨hψinj, hψsurj⟩
  let e2 : ↥X₁ ≃* ↥W := MulEquiv.ofBijective ψ hψbij
  have hφe2 : ∀ z : ↥X₁, ((e2 z : ↥W) : ↥J) = φm ⟨(z : X), hX₁K z.2⟩ := by
    intro z
    change ((ψ z : ↥W) : ↥J) = φm ⟨(z : X), hX₁K z.2⟩
    rfl
  let N : Subgroup ↥W := H.subgroupOf W
  let T₀ : Subgroup X := (N.map (e2.symm : ↥W →* ↥X₁)).map X₁.subtype
  have hT : T₀ ≤ X₁ := Subgroup.map_subtype_le _
  have hsubT : T₀.subgroupOf X₁ = N.map (e2.symm : ↥W →* ↥X₁) :=
    Subgroup.comap_map_eq_self_of_injective (f := X₁.subtype) X₁.subtype_injective _
  have hnorm : (T₀.subgroupOf X₁).Normal := by
    rw [hsubT]
    exact hHn.map (e2.symm : ↥W →* ↥X₁) e2.symm.surjective
  have hNsimple : IsSimpleGroup ↥N :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He eHW
  have eT : ↥T₀ ≃* ↥N :=
    (Subgroup.equivMapOfInjective (N.map (e2.symm : ↥W →* ↥X₁)) X₁.subtype
      X₁.subtype_injective).symm.trans
      (Subgroup.equivMapOfInjective N (e2.symm : ↥W →* ↥X₁) e2.symm.injective).symm
  have hTsimple : IsSimpleGroup ↥T₀ :=
    @MulEquiv.isSimpleGroup _ _ _ _ hNsimple eT
  have hTc : Nat.card ↥T₀ = 4030387200 :=
    (Nat.card_congr eT.toEquiv).trans hHc
  have hidxT : (T₀.subgroupOf X₁).index ∣ 2 := by
    rw [hsubT, Subgroup.index_map_equiv (H := N) e2.symm]
    exact hidx
  have hCK : Subgroup.centralizer (T₀ : Set X) ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    obtain ⟨hcT, hcK⟩ := Subgroup.mem_inf.mp hc
    let cK : ↥K := ⟨c, hcK⟩
    have hφc : φm cK ∈ Subgroup.centralizer (H : Set ↥J) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxW : x ∈ W := hHW hx
      let xW : ↥W := ⟨x, hxW⟩
      have hxN : xW ∈ N := Subgroup.mem_subgroupOf.mpr hx
      let y : ↥X₁ := e2.symm xW
      have hyN : y ∈ N.map (e2.symm : ↥W →* ↥X₁) :=
        Subgroup.mem_map_of_mem (e2.symm : ↥W →* ↥X₁) hxN
      have hyT : (y : X) ∈ T₀ := Subgroup.mem_map_of_mem X₁.subtype hyN
      let yK : ↥K := ⟨(y : X), hX₁K y.2⟩
      have hφy : φm yK = x := by
        have h1 : ((e2 y : ↥W) : ↥J) = φm yK := hφe2 y
        have h2 : (e2 y : ↥W) = xW := MulEquiv.apply_symm_apply e2 xW
        rw [← h1, h2]
      have hmul : yK * cK = cK * yK := by
        apply Subtype.ext
        simpa using hcT (y : X) hyT
      calc x * φm cK = φm yK * φm cK := by rw [← hφy]
        _ = φm (yK * cK) := (map_mul φm yK cK).symm
        _ = φm (cK * yK) := by rw [hmul]
        _ = φm cK * φm yK := map_mul φm cK yK
        _ = φm cK * x := by rw [hφy]
    have hφc1 : φm cK = 1 := by
      rw [hCH, Subgroup.mem_bot] at hφc
      exact hφc
    have hcK1 : cK = 1 := hφinj (by rw [hφc1, map_one])
    have hc1 : c = 1 := by
      have h := congrArg (fun z : ↥K => (z : X)) hcK1
      simpa [cK] using h
    exact Subgroup.mem_bot.mpr hc1
  exact ⟨T₀, hT, hnorm, hTsimple, hTc, hidxT, hCK⟩

theorem socle_of_fi24Prime (hb : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (hbr : CFSG.Quasithin.B113KDet.CatalogBridge)
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X}
    (h : ThreeNineHyp K E D X₁ 7 17)
    (hs : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .Fi24Prime) (hDK : D ≤ K) :
    IsSimpleGroup ↥(oPPrimeHull 17 X₁) ∧
      Subgroup.centralizer (oPPrimeHull 17 X₁ : Set X) ⊓ K = ⊥ := by
  obtain ⟨T₀, hT, hn, hs, hcard, hidx, hC⟩ :=
    exists_he_normal_of_fi24Prime hb hOrd hbr h hs hDK
  refine socle_of_centralizer_eq_bot h hT hn hs ?_ ?_ hC
  · rw [hcard]
    norm_num
  · intro h17
    have hidxpos : 0 < (T₀.subgroupOf X₁).index := Nat.pos_of_dvd_of_pos hidx (by norm_num)
    have hle : (T₀.subgroupOf X₁).index ≤ 2 := Nat.le_of_dvd (by norm_num) hidx
    have hle17 : 17 ≤ (T₀.subgroupOf X₁).index := Nat.le_of_dvd hidxpos h17
    omega

end CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp
