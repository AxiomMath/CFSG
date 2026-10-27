module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GroupTheory.SteinbergBKPNilpotentQuotientCore
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.IndexNormalSup

public section

namespace CFSG.GroupTheory

open scoped Pointwise

variable {H : Type*} [Group H] [Finite H] {K S : Subgroup H}

abbrev twoQuotientC (K S : Subgroup H) : Subgroup ↥(K ⊔ S) :=
  (S ⊓ Subgroup.centralizer (K : Set H)).subgroupOf (K ⊔ S)

abbrev twoQuotientY (K S : Subgroup H) (h : (twoQuotientC K S).Normal) : Type _ :=
  letI : (twoQuotientC K S).Normal := h
  ↥(K ⊔ S) ⧸ twoQuotientC K S

abbrev twoQuotientPi (K S : Subgroup H) (h : (twoQuotientC K S).Normal) :
    ↥(K ⊔ S) →* twoQuotientY K S h :=
  letI : (twoQuotientC K S).Normal := h
  QuotientGroup.mk' (twoQuotientC K S)

abbrev twoQuotientKY (K S : Subgroup H) (h : (twoQuotientC K S).Normal) :
    Subgroup (twoQuotientY K S h) :=
  (K.subgroupOf (K ⊔ S)).map (twoQuotientPi K S h)

abbrev twoQuotientSY (K S : Subgroup H) (h : (twoQuotientC K S).Normal) :
    Subgroup (twoQuotientY K S h) :=
  (S.subgroupOf (K ⊔ S)).map (twoQuotientPi K S h)

theorem twoQuotientK_normal (hSK : S ≤ Subgroup.normalizer (K : Set H)) :
    (K.subgroupOf (K ⊔ S)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : K ≤ K ⊔ S)).mpr
    (sup_le Subgroup.le_normalizer hSK)

theorem twoQuotientC_normal (hSK : S ≤ Subgroup.normalizer (K : Set H)) :
    (twoQuotientC K S).Normal := by
  let J := K ⊔ S
  let C := twoQuotientC K S
  have hKfix : ∀ y ∈ K.subgroupOf J, ∀ c ∈ C, y * c * y⁻¹ = c := by
    intro y hy c hc
    have hyK : ((y : J) : H) ∈ K := hy
    have hcC : ((c : J) : H) ∈ S ⊓ Subgroup.centralizer (K : Set H) := hc
    have hcomm : ((y : J) : H) * ((c : J) : H) = ((c : J) : H) * ((y : J) : H) :=
      Subgroup.mem_centralizer_iff.1 hcC.2 ((y : J) : H) hyK
    apply Subtype.ext
    change ((y : J) : H) * ((c : J) : H) * ((y : J) : H)⁻¹ = ((c : J) : H)
    rw [hcomm]
    group
  have hKle : (K.subgroupOf J) ≤ Subgroup.normalizer (C : Set J) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      rw [hKfix x hx c hc]
      exact hc
    · intro hc
      have hx' : (x : J)⁻¹ ∈ K.subgroupOf J := (K.subgroupOf J).inv_mem hx
      have hceq : c = (x : J) * c * (x : J)⁻¹ := by
        have h := hKfix ((x : J)⁻¹) hx' ((x : J) * c * (x : J)⁻¹) hc
        calc c = (x : J)⁻¹ * ((x : J) * c * (x : J)⁻¹) * ((x : J)⁻¹)⁻¹ := by group
          _ = (x : J) * c * (x : J)⁻¹ := h
      rw [hceq]
      exact hc
  have hSfix : ∀ y ∈ S.subgroupOf J, ∀ c ∈ C, y * c * y⁻¹ ∈ C := by
    intro y hy c hc
    have hyS : ((y : J) : H) ∈ S := hy
    have hcC : ((c : J) : H) ∈ S ⊓ Subgroup.centralizer (K : Set H) := hc
    have hmemS : ((y : J) : H) * ((c : J) : H) * ((y : J) : H)⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem hyS hcC.1) (S.inv_mem hyS)
    have hmemC : ((y : J) : H) * ((c : J) : H) * ((y : J) : H)⁻¹ ∈
        Subgroup.centralizer (K : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hyN : ((y : J) : H) ∈ Subgroup.normalizer (K : Set H) := hSK hyS
      have hk' : ((y : J) : H)⁻¹ * k * ((y : J) : H) ∈ K := by
        have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hyN) k).1 hk
        simpa using h
      have hcomm := Subgroup.mem_centralizer_iff.1 hcC.2 _ hk'
      calc k * (((y : J) : H) * ((c : J) : H) * ((y : J) : H)⁻¹)
          = ((y : J) : H) * ((((y : J) : H)⁻¹ * k * ((y : J) : H)) *
              ((c : J) : H)) * ((y : J) : H)⁻¹ := by group
        _ = ((y : J) : H) * (((c : J) : H) *
              (((y : J) : H)⁻¹ * k * ((y : J) : H))) * ((y : J) : H)⁻¹ := by rw [hcomm]
        _ = (((y : J) : H) * ((c : J) : H) * ((y : J) : H)⁻¹) * k := by group
    exact ⟨hmemS, hmemC⟩
  have hSle : (S.subgroupOf J) ≤ Subgroup.normalizer (C : Set J) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact hSfix x hx c hc
    · intro hc
      have hx' : (x : J)⁻¹ ∈ S.subgroupOf J := (S.subgroupOf J).inv_mem hx
      have h := hSfix ((x : J)⁻¹) hx' ((x : J) * c * (x : J)⁻¹) hc
      have hceq : (x : J)⁻¹ * ((x : J) * c * (x : J)⁻¹) * ((x : J)⁻¹)⁻¹ = c := by
        group
      rwa [hceq] at h
  have hsup : (K.subgroupOf J) ⊔ (S.subgroupOf J) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : K ≤ J) (le_sup_right : S ≤ J),
      Subgroup.subgroupOf_self]
  have hle : (⊤ : Subgroup J) ≤ Subgroup.normalizer (C : Set J) := by
    rw [← hsup]
    exact sup_le hKle hSle
  exact Subgroup.normalizer_eq_top_iff.mp (top_unique hle)

theorem twoQuotientK_inf_C_eq_bot (hZ : Odd (Nat.card (Subgroup.center ↥K)))
    (hS : IsPGroup 2 S) (hSK : S ≤ Subgroup.normalizer (K : Set H)) :
    (K.subgroupOf (K ⊔ S)) ⊓ twoQuotientC K S = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxS : ((x : ↥(K ⊔ S)) : H) ∈ S := hxC.1
  have hxZ : ((x : ↥(K ⊔ S)) : H) ∈ (Subgroup.center ↥K).map K.subtype := by
    refine Subgroup.mem_map.2 ⟨⟨((x : ↥(K ⊔ S)) : H), hxK⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext
      (Subgroup.mem_centralizer_iff.1 hxC.2 (k : H) k.2)
  have hodd : Odd (Nat.card ((Subgroup.center ↥K).map K.subtype)) := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hZ
  have hcop : Nat.Coprime (Nat.card ((Subgroup.center ↥K).map K.subtype)) 2 :=
    (Nat.coprime_two_left.2 hodd).symm
  have hone : ((x : ↥(K ⊔ S)) : H) = 1 :=
    CFSG.GroupTheory.SteinbergBK.eq_one_of_mem_of_mem hS hcop hxS hxZ
  exact Subtype.ext hone

theorem twoQuotient_mk_injective_K (hZ : Odd (Nat.card (Subgroup.center ↥K)))
    (hS : IsPGroup 2 S) (hSK : S ≤ Subgroup.normalizer (K : Set H)) :
    Function.Injective (fun x : ↥(K.subgroupOf (K ⊔ S)) =>
      twoQuotientPi K S (twoQuotientC_normal hSK) x) := by
  let C := twoQuotientC K S
  letI : C.Normal := twoQuotientC_normal hSK
  intro x y hxy
  have hker : ∀ z : ↥(K.subgroupOf (K ⊔ S)),
      twoQuotientPi K S (twoQuotientC_normal hSK) z = 1 → z = 1 := by
    intro z hz
    have hzC : (z : ↥(K ⊔ S)) ∈ C :=
      (QuotientGroup.eq_one_iff (z : ↥(K ⊔ S))).mp hz
    have hzbot : (z : ↥(K ⊔ S)) ∈ (K.subgroupOf (K ⊔ S)) ⊓ C := ⟨z.2, hzC⟩
    rw [show (K.subgroupOf (K ⊔ S)) ⊓ C = ⊥ from twoQuotientK_inf_C_eq_bot hZ hS hSK] at hzbot
    exact Subtype.ext (Subgroup.mem_bot.mp hzbot)
  have hmem : (x : ↥(K ⊔ S)) * (y : ↥(K ⊔ S))⁻¹ ∈ K.subgroupOf (K ⊔ S) :=
    (K.subgroupOf (K ⊔ S)).mul_mem x.2 ((K.subgroupOf (K ⊔ S)).inv_mem y.2)
  have hxy' : twoQuotientPi K S (twoQuotientC_normal hSK) (x : ↥(K ⊔ S)) =
      twoQuotientPi K S (twoQuotientC_normal hSK) (y : ↥(K ⊔ S)) := hxy
  have h1' : twoQuotientPi K S (twoQuotientC_normal hSK) (x : ↥(K ⊔ S)) *
      (twoQuotientPi K S (twoQuotientC_normal hSK) (y : ↥(K ⊔ S)))⁻¹ = 1 := by
    rw [hxy', mul_inv_cancel]
  have h1 : twoQuotientPi K S (twoQuotientC_normal hSK)
      (⟨(x : ↥(K ⊔ S)) * (y : ↥(K ⊔ S))⁻¹, hmem⟩ : ↥(K.subgroupOf (K ⊔ S))) = 1 := by
    simpa only [map_mul, map_inv] using h1'
  have h2 : (⟨(x : ↥(K ⊔ S)) * (y : ↥(K ⊔ S))⁻¹, hmem⟩ :
      ↥(K.subgroupOf (K ⊔ S))) = 1 := hker _ h1
  have h3 : (x : ↥(K ⊔ S)) * (y : ↥(K ⊔ S))⁻¹ = 1 := congrArg Subtype.val h2
  exact Subtype.ext (mul_inv_eq_one.mp h3)

theorem twoQuotientK_nonempty_equiv_K (hZ : Odd (Nat.card (Subgroup.center ↥K)))
    (hS : IsPGroup 2 S) (hSK : S ≤ Subgroup.normalizer (K : Set H)) :
    Nonempty (↥(twoQuotientKY K S (twoQuotientC_normal hSK)) ≃* ↥K) := by
  let hC := twoQuotientC_normal hSK
  let C := twoQuotientC K S
  letI : C.Normal := hC
  let K₀ : Subgroup ↥(K ⊔ S) := K.subgroupOf (K ⊔ S)
  let K_Y : Subgroup (twoQuotientY K S hC) := K₀.map (twoQuotientPi K S hC)
  let φ : ↥K₀ →* ↥K_Y :=
    { toFun := fun x => ⟨twoQuotientPi K S hC x, Subgroup.mem_map_of_mem _ x.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro x y; apply Subtype.ext; simp }
  have hinj : Function.Injective φ := by
    intro x y hxy
    exact twoQuotient_mk_injective_K hZ hS hSK (congrArg Subtype.val hxy)
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e : ↥K₀ ≃* ↥K_Y := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  exact ⟨e.symm.trans (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ S))⟩

theorem twoQuotientKY_normal (hSK : S ≤ Subgroup.normalizer (K : Set H)) :
    letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
    (twoQuotientKY K S (twoQuotientC_normal hSK)).Normal := by
  letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
  exact (twoQuotientK_normal hSK).map _ (QuotientGroup.mk'_surjective _)


theorem twoQuotientSY_isPGroup (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set H)) :
    letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
    IsPGroup 2 (twoQuotientSY K S (twoQuotientC_normal hSK)) := by
  letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
  let J := K ⊔ S
  have h : IsPGroup 2 ((S.subgroupOf J).map (twoQuotientPi K S (twoQuotientC_normal hSK))) :=
    (hS.comap_subtype (K := J)).map _
  exact h

theorem twoQuotientY_quotient_KY_isPGroup (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set H)) :
    letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
    letI : (twoQuotientKY K S (twoQuotientC_normal hSK)).Normal :=
      twoQuotientKY_normal hSK
    IsPGroup 2 (twoQuotientY K S (twoQuotientC_normal hSK) ⧸
      twoQuotientKY K S (twoQuotientC_normal hSK)) := by
  letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
  let J := K ⊔ S
  let C := twoQuotientC K S
  let Y := ↥J ⧸ C
  let π := QuotientGroup.mk' C
  let K_Y : Subgroup Y := (K.subgroupOf J).map π
  let S_Y : Subgroup Y := (S.subgroupOf J).map π
  have hKJ : (K.subgroupOf J).Normal := twoQuotientK_normal hSK
  haveI : (K.subgroupOf J).Normal := hKJ
  haveI hKY : K_Y.Normal := twoQuotientKY_normal hSK
  have hsup : (K.subgroupOf J) ⊔ (S.subgroupOf J) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : K ≤ J) (le_sup_right : S ≤ J),
      Subgroup.subgroupOf_self]
  have hSY2 : IsPGroup 2 ↥S_Y := twoQuotientSY_isPGroup hS hSK
  let Q := Y ⧸ K_Y
  let f : ↥S_Y →* Q := (QuotientGroup.mk' K_Y).comp S_Y.subtype
  have hf_surj : Function.Surjective f := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K_Y x
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective C y
    have hj : j ∈ (K.subgroupOf J) ⊔ (S.subgroupOf J) := by
      rw [hsup]
      trivial
    obtain ⟨k, hk, s, hs, hks⟩ := Subgroup.mem_sup_of_normal_left.mp hj
    refine ⟨⟨π s, Subgroup.mem_map_of_mem π hs⟩, ?_⟩
    change QuotientGroup.mk' K_Y (π s) = QuotientGroup.mk' K_Y (π j)
    rw [← hks, map_mul]
    have hkY : QuotientGroup.mk' K_Y (π k) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_map_of_mem π hk)
    rw [map_mul, hkY, one_mul]
  exact IsPGroup.of_surjective hSY2 f hf_surj

theorem twoQuotientKY_index_eq_pow (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set H)) :
    letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
    ∃ n, (twoQuotientKY K S (twoQuotientC_normal hSK)).index = 2 ^ n := by
  letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
  let Y := twoQuotientY K S (twoQuotientC_normal hSK)
  let K_Y := twoQuotientKY K S (twoQuotientC_normal hSK)
  haveI hKY : K_Y.Normal := twoQuotientKY_normal hSK
  have hquot : IsPGroup 2 (Y ⧸ K_Y) := twoQuotientY_quotient_KY_isPGroup hS hSK
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := Y ⧸ K_Y)).mp hquot
  exact ⟨n, by rw [Subgroup.index_eq_card, hn]⟩

theorem twoQuotientSY_sylow (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set H))
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ K) K) :
    letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
    ∃ Sbar : Sylow 2 (twoQuotientY K S (twoQuotientC_normal hSK)),
      (Sbar : Subgroup (twoQuotientY K S (twoQuotientC_normal hSK))) =
        twoQuotientSY K S (twoQuotientC_normal hSK) := by
  letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let J := K ⊔ S
  let C := twoQuotientC K S
  have hKJ : (K.subgroupOf J).Normal := twoQuotientK_normal hSK
  have hsup : (K.subgroupOf J) ⊔ (S.subgroupOf J) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : K ≤ J) (le_sup_right : S ≤ J),
      Subgroup.subgroupOf_self]
  have hinf : (K.subgroupOf J) ⊓ (S.subgroupOf J) = (K ⊓ S).subgroupOf J := by
    change Subgroup.comap J.subtype K ⊓ Subgroup.comap J.subtype S =
      Subgroup.comap J.subtype (K ⊓ S)
    rw [Subgroup.comap_inf]
  have hSindex : (S.subgroupOf J).index = (K ⊓ S).relIndex K := by
    rw [CFSG.GorensteinWalter.index_eq_relIndex_inf_of_normal_sup (K.subgroupOf J)
      (S.subgroupOf J) hKJ hsup, hinf,
      Subgroup.relIndex_subgroupOf (H := K ⊓ S) (K := K) (L := J)
        (le_sup_left : K ≤ J)]
  have hodd : ¬ 2 ∣ (S.subgroupOf J).index := by
    rw [hSindex, inf_comm]
    exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hSyl).2.2
  have hSJp : IsPGroup 2 (S.subgroupOf J) := hS.comap_subtype (K := J)
  let Sol : Sylow 2 J := hSJp.toSylow hodd
  have hSol : (Sol : Subgroup J) = S.subgroupOf J := IsPGroup.toSylow_coe hSJp hodd
  let Sbar : Sylow 2 (twoQuotientY K S (twoQuotientC_normal hSK)) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective C) Sol
  have hSbar : (Sbar : Subgroup (twoQuotientY K S (twoQuotientC_normal hSK))) =
      twoQuotientSY K S (twoQuotientC_normal hSK) := by
    rw [Sylow.coe_mapSurjective, hSol]
  exact ⟨Sbar, hSbar⟩

theorem twoQuotientSY_isSylowIn (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set H))
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ K) K) :
    letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
    CFSG.Quasithin.IsSylowIn 2 (twoQuotientSY K S (twoQuotientC_normal hSK)) ⊤ := by
  letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Sbar, hSbar⟩ := twoQuotientSY_sylow hS hSK hSyl
  refine ⟨le_top, ?_, ?_⟩
  · rw [← hSbar]
    exact Sbar.isPGroup'
  · rw [Subgroup.relIndex_top_right, ← hSbar]
    exact Sbar.not_dvd_index

theorem twoQuotientSY_inf_centralizer_eq_bot (hZ : Odd (Nat.card (Subgroup.center ↥K)))
    (hS : IsPGroup 2 S) (hSK : S ≤ Subgroup.normalizer (K : Set H)) :
    letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
    twoQuotientSY K S (twoQuotientC_normal hSK) ⊓
      Subgroup.centralizer (twoQuotientKY K S (twoQuotientC_normal hSK) : Set
        (twoQuotientY K S (twoQuotientC_normal hSK))) = ⊥ := by
  letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
  let J := K ⊔ S
  let C := twoQuotientC K S
  let Y := ↥J ⧸ C
  let π := QuotientGroup.mk' C
  let K_Y : Subgroup Y := (K.subgroupOf J).map π
  let S_Y : Subgroup Y := (S.subgroupOf J).map π
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨s, hs, hπs⟩ := Subgroup.mem_map.1 hyS
  rw [← hπs] at hyC
  have hsS : ((s : J) : H) ∈ S := hs
  have hscent : ((s : J) : H) ∈ Subgroup.centralizer (K : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    let k_J : J := ⟨k, Subgroup.mem_sup_left hk⟩
    have hkJ : k_J ∈ K.subgroupOf J := Subgroup.mem_subgroupOf.mpr hk
    have hkY : π k_J ∈ K_Y := Subgroup.mem_map_of_mem π hkJ
    have hcomm : π k_J * π s = π s * π k_J :=
      Subgroup.mem_centralizer_iff.1 hyC (π k_J) hkY
    have hker : k_J * s * k_J⁻¹ * s⁻¹ ∈ C := by
      rw [← QuotientGroup.eq_one_iff (k_J * s * k_J⁻¹ * s⁻¹)]
      calc π (k_J * s * k_J⁻¹ * s⁻¹) = π k_J * π s * (π k_J)⁻¹ * (π s)⁻¹ := by simp
        _ = 1 := by rw [hcomm]; group
    have hmemK : k_J * s * k_J⁻¹ * s⁻¹ ∈ K.subgroupOf J := by
      rw [Subgroup.mem_subgroupOf]
      have hsN : ((s : J) : H) ∈ Subgroup.normalizer (K : Set H) := hSK hsS
      have h1 : ((s : J) : H) * k⁻¹ * ((s : J) : H)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.1 hsN k⁻¹).1 (K.inv_mem hk)
      have h2 : (((k_J * s * k_J⁻¹ * s⁻¹ : J)) : H) =
          k * (((s : J) : H) * k⁻¹ * ((s : J) : H)⁻¹) := by
        change k * ((s : J) : H) * k⁻¹ * ((s : J) : H)⁻¹ =
          k * (((s : J) : H) * k⁻¹ * ((s : J) : H)⁻¹)
        group
      rw [h2]
      exact K.mul_mem hk h1
    have hmemCbot : k_J * s * k_J⁻¹ * s⁻¹ ∈ (K.subgroupOf J) ⊓ C := ⟨hmemK, hker⟩
    rw [twoQuotientK_inf_C_eq_bot hZ hS hSK] at hmemCbot
    have hone : k_J * s * k_J⁻¹ * s⁻¹ = 1 := Subgroup.mem_bot.mp hmemCbot
    have hconj : k * ((s : J) : H) = ((s : J) : H) * k := by
      have h := congrArg (fun z : J => (z : H)) hone
      change k * ((s : J) : H) * k⁻¹ * ((s : J) : H)⁻¹ = 1 at h
      calc k * ((s : J) : H) = (k * ((s : J) : H) * k⁻¹ * ((s : J) : H)⁻¹) *
            (((s : J) : H) * k) := by group
        _ = ((s : J) : H) * k := by rw [h, one_mul]
    exact hconj
  have hsC : (s : J) ∈ C := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨hsS, hscent⟩
  have hπs1 : π s = 1 := (QuotientGroup.eq_one_iff (s : J)).mpr hsC
  rw [hπs1] at hπs
  exact hπs.symm


theorem twoQuotient_centralizer_eq_center (hZ : Odd (Nat.card (Subgroup.center ↥K)))
    (hS : IsPGroup 2 S) (hSK : S ≤ Subgroup.normalizer (K : Set H))
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ K) K) :
    letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
    Subgroup.centralizer (twoQuotientKY K S (twoQuotientC_normal hSK) : Set
        (twoQuotientY K S (twoQuotientC_normal hSK))) =
      (Subgroup.center ↥(twoQuotientKY K S (twoQuotientC_normal hSK))).map
        (twoQuotientKY K S (twoQuotientC_normal hSK)).subtype := by
  letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
  let J := K ⊔ S
  let C := twoQuotientC K S
  let Y := ↥J ⧸ C
  let π := QuotientGroup.mk' C
  let K_Y : Subgroup Y := (K.subgroupOf J).map π
  let S_Y : Subgroup Y := (S.subgroupOf J).map π
  let Z : Subgroup Y := (Subgroup.center ↥K_Y).map K_Y.subtype
  let CY : Subgroup Y := Subgroup.centralizer (K_Y : Set Y)
  haveI hKYn : K_Y.Normal := twoQuotientKY_normal hSK
  haveI hCYn : CY.Normal := Subgroup.normal_centralizer
  have hCYinf : CY ⊓ K_Y = Z := by
    rw [inf_comm, CFSG.GroupTheory.inf_centralizer_eq_map_center K_Y]
  have hZodd : Odd (Nat.card Z) := by
    have hcardZ : Nat.card Z = Nat.card (Subgroup.center ↥K_Y) :=
      Subgroup.card_map_of_injective K_Y.subtype_injective
    obtain ⟨e⟩ := twoQuotientK_nonempty_equiv_K hZ hS hSK
    have hcardC : Nat.card (Subgroup.center ↥K_Y) = Nat.card (Subgroup.center ↥K) :=
      Nat.card_congr (Subgroup.centerCongr e).toEquiv
    rw [hcardZ, hcardC]
    exact hZ
  have hZleCY : Z ≤ CY := by
    rintro z ⟨zc, hzc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc ⟨k, hk⟩)
  have hZcentralCY : Z.subgroupOf CY ≤ Subgroup.center ↥CY := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    have hzZ : (z : Y) ∈ Z := Subgroup.mem_subgroupOf.mp hz
    have hzK : (z : Y) ∈ K_Y := by
      obtain ⟨zc, hzc, hzc'⟩ := Subgroup.mem_map.1 hzZ
      rw [← hzc']
      exact zc.2
    have hcomm : (z : Y) * (c : Y) = (c : Y) * (z : Y) :=
      Subgroup.mem_centralizer_iff.1 c.2 (z : Y) hzK
    exact hcomm.symm
  have hZnormalCY : (Z.subgroupOf CY).Normal := Subgroup.normal_of_le_center hZcentralCY
  let f : ↥CY →* (Y ⧸ K_Y) := (QuotientGroup.mk' K_Y).comp CY.subtype
  have hfker : f.ker = Z.subgroupOf CY := by
    ext c
    constructor
    · intro hc
      rw [MonoidHom.mem_ker] at hc
      have hcK : (c : Y) ∈ K_Y := (QuotientGroup.eq_one_iff (c : Y)).mp hc
      have hcinf : (c : Y) ∈ CY ⊓ K_Y := ⟨c.2, hcK⟩
      rwa [hCYinf] at hcinf
    · intro hc
      rw [MonoidHom.mem_ker]
      have hcZ : (c : Y) ∈ Z := Subgroup.mem_subgroupOf.mp hc
      obtain ⟨zc, hzc, hcZ'⟩ := Subgroup.mem_map.1 hcZ
      change QuotientGroup.mk' K_Y (c : Y) = 1
      rw [← hcZ']
      exact (QuotientGroup.eq_one_iff _).mpr zc.2
  have hYKquot : IsPGroup 2 (Y ⧸ K_Y) := twoQuotientY_quotient_KY_isPGroup hS hSK
  have hRange : IsPGroup 2 ↥f.range :=
    hYKquot.of_injective f.range.subtype Subtype.val_injective
  have hquotZ : IsPGroup 2 (↥CY ⧸ Z.subgroupOf CY) := by
    have h1 : IsPGroup 2 (↥CY ⧸ f.ker) :=
      hRange.of_equiv (QuotientGroup.quotientKerEquivRange f).symm
    exact h1.of_equiv (QuotientGroup.quotientMulEquivOfEq hfker)
  let CYbar : Type _ := ↥CY ⧸ Z.subgroupOf CY
  let qbar : ↥CY →* CYbar := QuotientGroup.mk' (Z.subgroupOf CY)
  let Q0 : Sylow 2 ↥CY := Classical.choice (Sylow.nonempty (p := 2) (G := ↥CY))
  let Qbar : Sylow 2 CYbar := Sylow.mapSurjective (QuotientGroup.mk'_surjective _) Q0
  have hQbarTop : (Qbar : Subgroup CYbar) = ⊤ := by
    have hmax := Qbar.is_maximal' (hquotZ.to_subgroup ⊤) le_top
    exact hmax.symm
  have hsplitCY : Z.subgroupOf CY ⊔ (Q0 : Subgroup ↥CY) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    have hcQ : qbar c ∈ (Qbar : Subgroup CYbar) := by
      rw [hQbarTop]
      trivial
    obtain ⟨s, hs, hse⟩ := hcQ
    have hmem : c * s⁻¹ ∈ Z.subgroupOf CY := by
      rw [← QuotientGroup.eq_one_iff (c * s⁻¹), QuotientGroup.mk_mul,
        QuotientGroup.mk_inv]
      change qbar c * (qbar s)⁻¹ = 1
      rw [hse, mul_inv_cancel]
    exact (Subgroup.mem_sup_of_normal_left).2 ⟨c * s⁻¹, hmem, s, hs, by group⟩
  let Q : Subgroup Y := (Q0 : Subgroup ↥CY).map CY.subtype
  have hQ2 : IsPGroup 2 Q := Q0.isPGroup'.map CY.subtype
  have hQleCY : Q ≤ CY := Subgroup.map_subtype_le _
  have hsplit : Z ⊔ Q = CY := by
    have h := congrArg (Subgroup.map CY.subtype) hsplitCY
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hZleCY, Subgroup.map_top,
      Subgroup.range_subtype] at h
    exact h
  have hZleNormQ : Z ≤ Subgroup.normalizer (Q : Set Y) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hfix : ∀ q ∈ Q, (MulAut.conj z) q = q := by
      intro q hq
      have hzK : (z : Y) ∈ K_Y := by
        obtain ⟨zc, hzc, hzc'⟩ := Subgroup.mem_map.1 hz
        rw [← hzc']
        exact zc.2
      have hcomm : (z : Y) * (q : Y) = (q : Y) * (z : Y) :=
        Subgroup.mem_centralizer_iff.1 (hQleCY hq) (z : Y) hzK
      show z * q * z⁻¹ = q
      rw [hcomm]
      group
    apply le_antisymm
    · rintro q ⟨q', hq', rfl⟩
      simpa [hfix q' hq'] using hq'
    · intro q hq
      exact ⟨q, hq, hfix q hq⟩
  have hQnormCY : (Q.subgroupOf CY).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQleCY).mpr
    rw [← hsplit]
    refine sup_le hZleNormQ Subgroup.le_normalizer
  have hQZbot : Q ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxQ, hxZ⟩ := Subgroup.mem_inf.mp hx
    have hcop : Nat.Coprime (Nat.card Z) 2 := (Nat.coprime_two_left.2 hZodd).symm
    exact CFSG.GroupTheory.SteinbergBK.eq_one_of_mem_of_mem hQ2 hcop hxQ hxZ
  have hQsubZ : Q.subgroupOf Z = ⊥ := by
    rw [← Subgroup.inf_subgroupOf_right Q Z, hQZbot, Subgroup.bot_subgroupOf]
  have hQindexOdd : ¬ 2 ∣ (Q.subgroupOf CY).index := by
    have hcommZQ : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z := by
      intro z hz q hq
      have hzK : (z : Y) ∈ K_Y := by
        obtain ⟨zc, hzc, hzc'⟩ := Subgroup.mem_map.1 hz
        rw [← hzc']
        exact zc.2
      exact Subgroup.mem_centralizer_iff.1 (hQleCY hq) (z : Y) hzK
    have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Z Q hcommZQ).1
    rw [hsplit, inf_comm, hQZbot] at hprod
    simp at hprod
    have hcardSub : Nat.card ↥(Q.subgroupOf CY) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleCY).toEquiv
    have hcardCY : Nat.card CY = Nat.card (CY ⧸ Q.subgroupOf CY) * Nat.card Q := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup, hcardSub]
    have hcard : Nat.card (CY ⧸ Q.subgroupOf CY) = Nat.card Z := by
      have hEq : Nat.card Z * Nat.card Q =
          Nat.card (CY ⧸ Q.subgroupOf CY) * Nat.card Q := by
        rw [← hprod, hcardCY]
      exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos hEq).symm
    rw [Subgroup.index_eq_card, hcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 (Nat.coprime_two_left.2 hZodd)
  have hQsub2 : IsPGroup 2 (Q.subgroupOf CY) := hQ2.comap_subtype
  let QS : Sylow 2 ↥CY := hQsub2.toSylow hQindexOdd
  have hQSc : (QS : Subgroup ↥CY) = Q.subgroupOf CY := IsPGroup.toSylow_coe hQsub2 hQindexOdd
  have hQSn : (QS : Subgroup ↥CY).Normal := by
    rw [hQSc]
    exact hQnormCY
  have hQSchar : (QS : Subgroup ↥CY).Characteristic := Sylow.characteristic_of_normal QS hQSn
  have hQchar : (Q.subgroupOf CY).Characteristic := by
    rwa [hQSc] at hQSchar
  have hQnormalY : Q.Normal := by
    haveI : (Q.subgroupOf CY).Characteristic := hQchar
    have h := ConjAct.normal_of_characteristic_of_normal (H := CY) (K := Q.subgroupOf CY)
    rwa [Subgroup.map_subgroupOf_eq_of_le hQleCY] at h
  haveI : Q.Normal := hQnormalY
  obtain ⟨Sbar, hSbarCoe⟩ := twoQuotientSY_sylow hS hSK hSyl
  have hQleSY : Q ≤ S_Y := by
    have := hQ2.le_sylow_of_normal Sbar
    rwa [hSbarCoe] at this
  have hQleInter : Q ≤ S_Y ⊓ CY := le_inf hQleSY hQleCY
  rw [twoQuotientSY_inf_centralizer_eq_bot hZ hS hSK] at hQleInter
  have hQbot : Q = ⊥ := le_bot_iff.mp hQleInter
  change CY = Z
  rw [← hsplit, hQbot, sup_bot_eq]


theorem twoQuotient_lift_subgroup (hZ : Odd (Nat.card (Subgroup.center ↥K)))
    (hS : IsPGroup 2 S) (hSK : S ≤ Subgroup.normalizer (K : Set H)) :
    letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
    ∀ {E_Y : Subgroup (twoQuotientY K S (twoQuotientC_normal hSK))},
      E_Y ≤ twoQuotientKY K S (twoQuotientC_normal hSK) →
        ∃ E : Subgroup H, E ≤ K ∧ Nonempty (↥E ≃* ↥E_Y) ∧
          E = ((E_Y.comap (twoQuotientPi K S (twoQuotientC_normal hSK)) ⊓
            K.subgroupOf (K ⊔ S)).map (K ⊔ S).subtype) := by
  letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
  intro E_Y hEY
  let J := K ⊔ S
  let C := twoQuotientC K S
  let Y := ↥J ⧸ C
  let π := QuotientGroup.mk' C
  let K_Y : Subgroup Y := (K.subgroupOf J).map π
  let X : Subgroup J := E_Y.comap π ⊓ K.subgroupOf J
  let φ : ↥X →* ↥E_Y :=
    { toFun := fun x => ⟨π x, (Subgroup.mem_inf.mp x.2).1⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro x y; apply Subtype.ext; simp }
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hπ : π (x : J) = π (y : J) := congrArg Subtype.val hxy
    have hxK : (x : J) ∈ K.subgroupOf J := (Subgroup.mem_inf.mp x.2).2
    have hyK : (y : J) ∈ K.subgroupOf J := (Subgroup.mem_inf.mp y.2).2
    have h := twoQuotient_mk_injective_K hZ hS hSK
      (a₁ := (⟨(x : J), hxK⟩ : ↥(K.subgroupOf J)))
      (a₂ := (⟨(y : J), hyK⟩ : ↥(K.subgroupOf J))) hπ
    have hxyJ : (x : J) = (y : J) :=
      congrArg (fun z : ↥(K.subgroupOf J) => (z : J)) h
    exact Subtype.ext hxyJ
  have hsurj : Function.Surjective φ := by
    intro e
    have heK : (e : Y) ∈ K_Y := hEY e.2
    obtain ⟨k, hkK, hk⟩ := Subgroup.mem_map.1 heK
    have hkEY : k ∈ E_Y.comap π := by
      rw [Subgroup.mem_comap]
      rw [hk]
      exact e.2
    exact ⟨⟨k, Subgroup.mem_inf.mpr ⟨hkEY, hkK⟩⟩, Subtype.ext hk⟩
  let eX : ↥X ≃* ↥E_Y := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  let E : Subgroup H := X.map J.subtype
  have hEK : E ≤ K := by
    rintro e ⟨x, hxX, rfl⟩
    exact (Subgroup.mem_inf.mp hxX).2
  refine ⟨E, hEK, ⟨(Subgroup.equivMapOfInjective X J.subtype J.subtype_injective).symm.trans eX⟩, rfl⟩


theorem twoQuotient_lift_pgroup_permutes (hZ : Odd (Nat.card (Subgroup.center ↥K)))
    (hS : IsPGroup 2 S) (hSK : S ≤ Subgroup.normalizer (K : Set H))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
    ∀ {E_Y : Subgroup (twoQuotientY K S (twoQuotientC_normal hSK))},
      E_Y ≤ twoQuotientKY K S (twoQuotientC_normal hSK) →
      IsPGroup p ↥E_Y →
      (E_Y : Set (twoQuotientY K S (twoQuotientC_normal hSK))) *
          (twoQuotientSY K S (twoQuotientC_normal hSK) : Set
            (twoQuotientY K S (twoQuotientC_normal hSK))) =
        (twoQuotientSY K S (twoQuotientC_normal hSK) : Set
            (twoQuotientY K S (twoQuotientC_normal hSK))) *
          (E_Y : Set (twoQuotientY K S (twoQuotientC_normal hSK))) →
      ∃ E : Subgroup H, E ≤ K ∧ Nonempty (↥E ≃* ↥E_Y) ∧ IsPGroup p ↥E ∧
        (E : Set H) * (S : Set H) = (S : Set H) * (E : Set H) := by
  letI : (twoQuotientC K S).Normal := twoQuotientC_normal hSK
  intro E_Y hEY hEp hperm
  obtain ⟨E, hEK, ⟨eE⟩, hEeq⟩ := twoQuotient_lift_subgroup hZ hS hSK hEY
  have hEpE : IsPGroup p ↥E := hEp.of_equiv eE.symm
  let J := K ⊔ S
  let C := twoQuotientC K S
  let Y := ↥J ⧸ C
  let π := QuotientGroup.mk' C
  let K_Y : Subgroup Y := (K.subgroupOf J).map π
  let S_Y : Subgroup Y := (S.subgroupOf J).map π
  let X : Subgroup J := E_Y.comap π ⊓ K.subgroupOf J
  have hC_le_SJ : C ≤ S.subgroupOf J := by
    intro c hc
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hc)).1
  have hCnormX : ∀ c ∈ C, ∀ x ∈ X, c * x * c⁻¹ ∈ X := by
    intro c hc x hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_comap]
      have hc1 : π c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
      rw [map_mul, map_mul, map_inv, hc1, one_mul, inv_one, mul_one]
      exact Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hx).1
    · rw [Subgroup.mem_subgroupOf]
      have hcS : ((c : J) : H) ∈ S :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hc)).1
      have hxK : ((x : J) : H) ∈ K :=
        (Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).2)
      have hcN : ((c : J) : H) ∈ Subgroup.normalizer (K : Set H) := hSK hcS
      have hcx : ((c : J) : H) * ((x : J) : H) * ((c : J) : H)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.1 hcN ((x : J) : H)).1 hxK
      simpa using hcx
  have hpermJ : (X : Set J) * (S.subgroupOf J : Set J) =
      (S.subgroupOf J : Set J) * (X : Set J) := by
    ext z
    constructor
    · rintro ⟨x, hxX, s, hsS, rfl⟩
      have hxEY : π x ∈ E_Y :=
        Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hxX).1
      have hsSY : π s ∈ S_Y := Subgroup.mem_map_of_mem π hsS
      have hmem : π (x * s) ∈ (E_Y : Set Y) * (S_Y : Set Y) :=
        Set.mem_mul.mpr ⟨π x, hxEY, π s, hsSY, (map_mul π x s).symm⟩
      rw [hperm] at hmem
      obtain ⟨s1, hs1, e1, he1, hs1e1⟩ := Set.mem_mul.mp hmem
      obtain ⟨s1', hs1', hπs1'⟩ := Subgroup.mem_map.1 hs1
      obtain ⟨k, hkK, hπk⟩ := Subgroup.mem_map.1 (hEY he1)
      have hkX : k ∈ X := by
        refine Subgroup.mem_inf.mpr ⟨?_, hkK⟩
        rw [Subgroup.mem_comap]
        rwa [hπk]
      have hπeq : π (s1' * k) = π (x * s) := by
        rw [map_mul, hπs1', hπk, hs1e1]
      let c : J := (s1' * k) / (x * s)
      have hcC : c ∈ C := QuotientGroup.eq_iff_div_mem.mp hπeq
      have hcS : c ∈ S.subgroupOf J := hC_le_SJ hcC
      have hdecomp : x * s = c⁻¹ * (s1' * k) := by
        dsimp [c]
        rw [div_eq_mul_inv]
        group
      refine Set.mem_mul.mpr ⟨c⁻¹ * s1', ?_, k, hkX, ?_⟩
      · exact (S.subgroupOf J).mul_mem ((S.subgroupOf J).inv_mem hcS) hs1'
      · show c⁻¹ * s1' * k = x * s
        rw [hdecomp]
        group
    · rintro ⟨s, hsS, x, hxX, rfl⟩
      have hxEY : π x ∈ E_Y :=
        Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hxX).1
      have hsSY : π s ∈ S_Y := Subgroup.mem_map_of_mem π hsS
      have hmem : π (s * x) ∈ (S_Y : Set Y) * (E_Y : Set Y) :=
        Set.mem_mul.mpr ⟨π s, hsSY, π x, hxEY, (map_mul π s x).symm⟩
      rw [← hperm] at hmem
      obtain ⟨e1, he1, s1, hs1, he1s1⟩ := Set.mem_mul.mp hmem
      obtain ⟨s1', hs1', hπs1'⟩ := Subgroup.mem_map.1 hs1
      obtain ⟨k, hkK, hπk⟩ := Subgroup.mem_map.1 (hEY he1)
      have hkX : k ∈ X := by
        refine Subgroup.mem_inf.mpr ⟨?_, hkK⟩
        rw [Subgroup.mem_comap]
        rwa [hπk]
      have hπeq : π (k * s1') = π (s * x) := by
        rw [map_mul, hπk, hπs1', he1s1]
      let c : J := (k * s1') / (s * x)
      have hcC : c ∈ C := QuotientGroup.eq_iff_div_mem.mp hπeq
      have hcS : c ∈ S.subgroupOf J := hC_le_SJ hcC
      have hdecomp : s * x = c⁻¹ * (k * s1') := by
        dsimp [c]
        rw [div_eq_mul_inv]
        group
      have hcInvC : c⁻¹ ∈ C := C.inv_mem hcC
      have hconjX : c⁻¹ * k * c ∈ X := by
        have := hCnormX (c⁻¹) hcInvC k hkX
        simpa using this
      refine Set.mem_mul.mpr ⟨c⁻¹ * k * c, hconjX, c⁻¹ * s1', ?_, ?_⟩
      · exact (S.subgroupOf J).mul_mem ((S.subgroupOf J).inv_mem hcS) hs1'
      · show c⁻¹ * k * c * (c⁻¹ * s1') = s * x
        rw [hdecomp]
        group
  have hEset : (E : Set H) = J.subtype '' (X : Set J) := by
    rw [hEeq]
    rfl
  have hSmap : (S.subgroupOf J).map J.subtype = S :=
    Subgroup.map_subgroupOf_eq_of_le (le_sup_right : S ≤ J)
  have hSset : (S : Set H) = J.subtype '' (S.subgroupOf J : Set J) := by
    change (S : Set H) = ↑((S.subgroupOf J).map J.subtype)
    rw [hSmap]
  have hpermH : (E : Set H) * (S : Set H) = (S : Set H) * (E : Set H) := by
    rw [hEset, hSset, ← Set.image_mul, hpermJ, ← Set.image_mul]
  exact ⟨E, hEK, ⟨eE⟩, hEpE, hpermH⟩

end CFSG.GroupTheory
