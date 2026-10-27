module

public import CFSG.GH74.Generic.Front.Transfer
public import CFSG.GH74.Generic.Lifting

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.Filter.ClassicalOdd Subgroup

theorem eq_one_or_self_of_mem_zpowers {H : Type*} [Group H] {z a : H} (h : z * z = 1)
    (ha : a ∈ Subgroup.zpowers z) : a = 1 ∨ a = z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, h, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, h, one_zpow, one_mul, zpow_one]

theorem exists_lift_twoSubgroup_contains {C : Type*} [Group C] [Finite C] (N : Subgroup C)
    [N.Normal] (Pb : Subgroup (C ⧸ N)) (hP : IsPGroup 2 Pb) (R : Subgroup C) (hR : IsPGroup 2 R)
    (hRle : R ≤ Pb.comap (QuotientGroup.mk' N)) :
    ∃ P : Subgroup C, IsPGroup 2 P ∧ R ≤ P ∧ P.map (QuotientGroup.mk' N) = Pb := by
  classical
  let Q : Subgroup C := Pb.comap (QuotientGroup.mk' N)
  let g : Q →* Pb := ((QuotientGroup.mk' N).comp Q.subtype).codRestrict Pb fun q => q.2
  have hg : Function.Surjective g := fun p => by
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective N (p : C ⧸ N)
    exact ⟨⟨c, show QuotientGroup.mk' N c ∈ Pb by rw [hc]; exact p.2⟩, Subtype.ext hc⟩
  have hR' : IsPGroup 2 ↥(R.subgroupOf Q) :=
    hR.of_injective (R.subgroupOfEquivOfLe hRle).toMonoidHom
      (R.subgroupOfEquivOfLe hRle).injective
  obtain ⟨S, hS⟩ := hR'.exists_le_sylow
  have hSg : (S : Subgroup Q).map g = ⊤ := by
    have h2 : (⊤ : Subgroup Pb) = (S.mapSurjective hg : Subgroup Pb) :=
      (S.mapSurjective hg).is_maximal' (hP.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h2
    exact h2.symm
  refine ⟨(S : Subgroup Q).map Q.subtype, S.isPGroup'.map Q.subtype, ?_, ?_⟩
  · intro r hr
    exact ⟨⟨r, hRle hr⟩, hS (by rw [Subgroup.mem_subgroupOf]; exact hr), rfl⟩
  · ext c
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact s.2
    · intro hc
      have : (⟨c, hc⟩ : Pb) ∈ (S : Subgroup Q).map g := hSg ▸ Subgroup.mem_top _
      obtain ⟨s, hs, hsc⟩ := this
      refine ⟨s, ⟨s, hs, rfl⟩, ?_⟩
      exact congrArg Subtype.val hsc

section B5

variable {G : Type} [Group G] [Finite G]

theorem noNoncentralInvolutionConj_of_data (hgen : Gen4 G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hKc : IsComponent K) (D : FrontData ↥K)
    (hSch : ∀ P : Subgroup (CentralizerBar x), GoodSub (ThreeModel ↥K) P → P ≤ K) :
    NoNoncentralInvolutionConj x K := by
  classical
  intro u hu hu2 hbK hbne hconj
  have hfr : Q8Frame ↥K := ⟨D.φ, D.inj, D.w, D.w_sq, D.w_swap⟩
  obtain ⟨hxK, -, hcentK, -, -, -⟩ := frame_B2 hgen hx hKc hfr
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  obtain ⟨c₀, hc₀⟩ := isConj_iff.1 hconj
  have hu1 : u ≠ 1 := by
    intro h
    apply hx1
    calc x = c₀⁻¹ * (c₀ * x * c₀⁻¹) * c₀ := by group
      _ = 1 := by rw [hc₀, h]; group
  obtain ⟨U, hU⟩ : ∃ U : ↥(centralizer ({x} : Set G)), U = ⟨u, hu⟩ := ⟨_, rfl⟩
  have hU2 : U * U = 1 := by rw [hU]; exact Subtype.ext hu2
  have hbar : barOf hu = proj x U := by rw [hU]; rfl
  have hbar2 : barOf hu * barOf hu = 1 := by
    rw [hbar, ← map_mul, hU2, map_one]
  have hbar1 : barOf hu ≠ 1 := by
    intro h
    rw [hbar] at h
    have hmem : U ∈ pPrimeCore 2 ↥(centralizer ({x} : Set G)) :=
      (QuotientGroup.eq_one_iff U).1 h
    have hP : IsPGroup 2 (zpowers U) :=
      isPGroup_zpowers_of_pow_two_pow_eq_one (n := 1) (by simpa [pow_two] using hU2)
    have h1 := eq_one_of_isPGroup_of_mem_pPrimeCore hP (Subgroup.mem_zpowers U) hmem
    exact hu1 (by rw [hU] at h1; exact congrArg Subtype.val h1)
  have hnc : (⟨barOf hu, hbK⟩ : ↥K) ∉ Subgroup.center ↥K := by
    intro hcen
    have hcent : barOf hu ∈ centralizer (K : Set (CentralizerBar x)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hcen ⟨k, hk⟩)
    rw [hcentK] at hcent
    rcases eq_one_or_self_of_mem_zpowers (xbar_mul_self hx) hcent with h | h
    · exact hbar1 h
    · exact hbne h
  obtain ⟨k, hk⟩ := D.oneClass ⟨barOf hu, hbK⟩ (Subtype.ext hbar2)
    (fun h => hbar1 (congrArg Subtype.val h)) hnc
  obtain ⟨kh, hkh⟩ := QuotientGroup.mk_surjective (k : CentralizerBar x)
  obtain ⟨U₁, hU₁⟩ : ∃ U₁ : ↥(centralizer ({x} : Set G)), U₁ = kh * U * kh⁻¹ := ⟨_, rfl⟩
  have hU₁2 : U₁ * U₁ = 1 := by
    rw [hU₁]
    calc kh * U * kh⁻¹ * (kh * U * kh⁻¹) = kh * (U * U) * kh⁻¹ := by group
      _ = 1 := by rw [hU2]; group
  have hproj₁ : proj x U₁ = ((D.φ (QuaternionGroup.a 2, 1) : ↥K) : CentralizerBar x) := by
    have h1 : proj x U₁ = proj x kh * barOf hu * (proj x kh)⁻¹ := by
      rw [hU₁, map_mul, map_mul, map_inv, hbar]
    have h2 : proj x kh = (k : CentralizerBar x) := hkh
    rw [h1, h2]
    have h3 := congrArg Subtype.val hk
    simpa using h3
  have hconj₁ : IsConj x (U₁ : G) := by
    refine hconj.trans (isConj_iff.2 ⟨(kh : G), ?_⟩)
    rw [hU₁, hU]
    rfl
  obtain ⟨c, hc'⟩ := isConj_iff.1 hconj₁
  have hc : c⁻¹ * (U₁ : G) * c = x := by
    rw [← hc']
    group
  let Φ : Q8 × Q8 →* CentralizerBar x := K.subtype.comp D.φ
  have hAP : IsPGroup 2 Φ.range := isPGroup_range_q8q8 Φ
  have hy₀ : proj x U₁ ∈ Φ.range := ⟨(QuaternionGroup.a 2, 1), hproj₁.symm⟩
  have hRP : IsPGroup 2 ↥(zpowers U₁) :=
    isPGroup_zpowers_of_pow_two_pow_eq_one (n := 1) (by simpa [pow_two] using hU₁2)
  have hRle : zpowers U₁ ≤
      Φ.range.comap (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G)))) := by
    rw [Subgroup.zpowers_le]
    exact hy₀
  obtain ⟨P, hP2, hRP', hPmap⟩ :=
    exists_lift_twoSubgroup_contains _ Φ.range hAP (zpowers U₁) hRP hRle
  have hU₁P : U₁ ∈ P := hRP' (Subgroup.mem_zpowers U₁)
  let lam : ↥P →* ↥Φ.range := ((proj x).comp P.subtype).codRestrict Φ.range (fun p => by
    have : (proj x) (p : ↥(centralizer ({x} : Set G))) ∈
        P.map (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G)))) :=
      Subgroup.mem_map_of_mem _ p.2
    rwa [hPmap] at this)
  have hlam_inj : Function.Injective lam := fun a b hab =>
    Subtype.ext (lift_twoSubgroup_injOn hP2 a.2 b.2 (congrArg Subtype.val hab))
  have hlam_surj : Function.Surjective lam := fun z => by
    have hz : (z : CentralizerBar x) ∈
        P.map (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({x} : Set G)))) := by
      rw [hPmap]
      exact z.2
    obtain ⟨p, hp, hpz⟩ := hz
    exact ⟨⟨p, hp⟩, Subtype.ext hpz⟩
  let e : ↥P ≃* ↥Φ.range := MulEquiv.ofBijective lam ⟨hlam_inj, hlam_surj⟩
  let ψ₀ : Q8 × Q8 →* ↥(centralizer ({x} : Set G)) :=
    P.subtype.comp (e.symm.toMonoidHom.comp Φ.rangeRestrict)
  have hψ₀proj : ∀ g, proj x (ψ₀ g) = Φ g := fun g => by
    have h1 : lam (e.symm (Φ.rangeRestrict g)) = Φ.rangeRestrict g := e.apply_symm_apply _
    exact congrArg Subtype.val h1
  have hψ₀mem : ∀ g, ψ₀ g ∈ P := fun g => (e.symm (Φ.rangeRestrict g)).2
  have hψ₀inj : Function.Injective ψ₀ := fun a b hab => by
    have h1 := congrArg (proj x) hab
    rw [hψ₀proj, hψ₀proj] at h1
    exact D.inj (Subtype.ext h1)
  have hψ₀U₁ : ψ₀ (QuaternionGroup.a 2, 1) = U₁ := by
    apply lift_twoSubgroup_injOn hP2 (hψ₀mem _) hU₁P
    have h1 := hψ₀proj (QuaternionGroup.a 2, 1)
    change proj x _ = proj x U₁
    rw [h1, hproj₁]
    rfl
  have hq8cent : ∀ g : Q8 × Q8, g * (QuaternionGroup.a 2, 1) = (QuaternionGroup.a 2, 1) * g := by
    intro g
    refine Prod.ext ?_ (by simp)
    have : ∀ y : Q8, y * QuaternionGroup.a 2 = QuaternionGroup.a 2 * y := by decide
    exact this g.1
  have hψ₀cent : ∀ g, ψ₀ g ∈ CU x U₁ := fun g => by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hψ₀U₁, ← map_mul, ← map_mul, hq8cent]
  let ψ₀' : Q8 × Q8 →* ↥(CU x U₁) := ψ₀.codRestrict _ hψ₀cent
  have hJgood : GoodSub (ThreeModel ↥K) (D.J.map K.subtype) := goodSub_map K.subtype D.good
  have hHc : ∀ h ∈ D.J.map K.subtype, h * proj x U₁ = proj x U₁ * h := by
    rintro _ ⟨j, hj, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (D.le_centralizer hj)
    rw [hproj₁]
    exact congrArg Subtype.val h1
  have hmain := transfer_bar x U₁ hU₁2 hc (ThreeModel ↥K) K hSch _ hJgood hHc
  have hKmem : ∀ g, transportHom x U₁ hc (ψ₀' g) ∈ K := by
    intro g
    apply hmain
    · have h1 : proj x ((ψ₀' g : ↥(CU x U₁)) : ↥(centralizer ({x} : Set G))) = Φ g := hψ₀proj g
      rw [h1]
      exact ⟨D.φ g, D.range_le ⟨g, rfl⟩, rfl⟩
    · obtain ⟨n, hn⟩ := hP2 ⟨ψ₀ g, hψ₀mem g⟩
      refine ⟨n, ?_⟩
      change (ψ₀ g) ^ (2 ^ n) = 1
      simpa using congrArg Subtype.val hn
  let ψ : Q8 × Q8 →* ↥K := ((transportHom x U₁ hc).comp ψ₀').codRestrict K hKmem
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : transportHom x U₁ hc (ψ₀' a) = transportHom x U₁ hc (ψ₀' b) :=
      congrArg Subtype.val hab
    let ψ₁ : Q8 × Q8 →* ↥(centralizer ({x} : Set G)) := (transportC x U₁ hc).comp ψ₀'
    have h2 : ψ₁ a = ψ₁ b :=
      lift_twoSubgroup_injOn (isPGroup_range_q8q8 ψ₁) ⟨a, rfl⟩ ⟨b, rfl⟩ h1
    have h3 : ψ₀' a = ψ₀' b := transportC_injective x U₁ hc h2
    exact hψ₀inj (congrArg (fun z : ↥(CU x U₁) => (z : ↥(centralizer ({x} : Set G)))) h3)
  have hψ1 : ψ (QuaternionGroup.a 2, 1) = ⟨xbar x, hxK⟩ := by
    apply Subtype.ext
    have h0 : ((ψ₀' (QuaternionGroup.a 2, 1) : ↥(CU x U₁)) : ↥(centralizer ({x} : Set G))) = U₁ :=
      hψ₀U₁
    have h2 : transportC x U₁ hc (ψ₀' (QuaternionGroup.a 2, 1)) = xH x := by
      apply Subtype.ext
      rw [transportC_val, h0]
      exact hc
    change proj x (transportC x U₁ hc (ψ₀' (QuaternionGroup.a 2, 1))) = xbar x
    rw [h2]
    rfl
  have hcen : (⟨xbar x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (xbar_comm x (g : CentralizerBar x))
  exact D.noCentral ψ hψinj (hψ1 ▸ hcen)

end B5

end CFSG.GH74.Generic
