module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDefs
public import CFSG.ClassicalInvolution.Balance.Quotient

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {t : G}

private theorem subgroupOf_map_eq_map_inclusion {X : Type*} [Group X] {C A : Subgroup X}
    (h : C ≤ A) (P : Subgroup ↥C) :
    (P.map C.subtype).subgroupOf A = P.map (Subgroup.inclusion h) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨p, hp, hpx⟩
    exact ⟨p, hp, Subtype.ext hpx⟩
  · rintro ⟨p, hp, hpx⟩
    exact ⟨p, hp, congrArg Subtype.val hpx⟩

theorem map_centralizerResidual_eq_of_l34SuzOdd (hS : L34SuzOddSetting A t) {d : G}
    (hdA : d ∈ A) (hd : d * d = 1)
    (hperf : Group.IsPerfect ↥(centralizer ({QuotientGroup.mk' (center ↥A) ⟨d, hdA⟩} :
      Set (↥A ⧸ center ↥A)))) :
    ((HarrisLit.centralizerResidual A d).subgroupOf A).map (QuotientGroup.mk' (center ↥A)) =
      centralizer ({QuotientGroup.mk' (center ↥A) ⟨d, hdA⟩} : Set (↥A ⧸ center ↥A)) := by
  set S := ↥A ⧸ Subgroup.center ↥A with hSdef
  set π : ↥A →* S := QuotientGroup.mk' (Subgroup.center ↥A) with hπdef
  set dA : ↥A := ⟨d, hdA⟩ with hdAdef
  set Cg : Subgroup G := A ⊓ Subgroup.centralizer ({d} : Set G) with hCgdef
  set Hg : Subgroup S := Subgroup.centralizer ({π dA} : Set S) with hHgdef
  have hCgA : Cg ≤ A := inf_le_left
  have hdA2 : dA * dA = 1 := Subtype.ext (by simpa using hd)
  have hdP : IsPGroup 2 (Subgroup.zpowers dA) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hdA2))
  have hCmap : (Subgroup.centralizer ({dA} : Set ↥A)).map π = Hg := by
    simpa [π, dA, Hg, S, hdAdef] using
      CFSG.ClassicalInvolution.Balance.map_centralizer_singleton_eq
        (N := Subgroup.center ↥A) hS.odd_card_center hdP
  have hmem : ∀ x : ↥Cg, π (Subgroup.inclusion hCgA x) ∈ Hg := by
    intro x
    have hx : Subgroup.inclusion hCgA x ∈ Subgroup.centralizer ({dA} : Set ↥A) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2.2)
    have := Subgroup.mem_map_of_mem π hx
    rwa [hCmap] at this
  let φ : ↥Cg →* ↥Hg := (π.comp (Subgroup.inclusion hCgA)).codRestrict Hg hmem
  have hφ : Function.Surjective φ := by
    intro y
    have hy : (y : S) ∈ (Subgroup.centralizer ({dA} : Set ↥A)).map π := by
      rw [hCmap]; exact y.2
    obtain ⟨c, hc, hcy⟩ := hy
    have hcd : (c : G) * d = d * (c : G) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)
    refine ⟨⟨c.1, ⟨c.2, ?_⟩⟩, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hcd
    · exact Subtype.ext hcy
  have hφrange : (perfectResidual ↥Cg).map φ = perfectResidual ↥Hg :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq φ hφ
  have hHgTop : perfectResidual ↥Hg = ⊤ := by
    simp [CFSG.perfectResidual]
  have hkey : (perfectResidual ↥Cg).map (π.comp (Subgroup.inclusion hCgA)) = Hg := by
    have hcomp : (π.comp (Subgroup.inclusion hCgA)) = Hg.subtype.comp φ := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, hφrange, hHgTop, Subgroup.map_top,
      Subgroup.range_subtype]
  change (((perfectResidual ↥Cg).map Cg.subtype).subgroupOf A).map π = Hg
  rw [subgroupOf_map_eq_map_inclusion hCgA, Subgroup.map_map]
  exact hkey

private theorem mem_of_isPGroup_of_odd_index {X : Type*} [Group X] [Finite X]
    {H : Subgroup X} [H.Normal] (hodd : Odd H.index) {x : X}
    (hx : IsPGroup 2 (Subgroup.zpowers x)) : x ∈ H := by
  obtain ⟨k, hk⟩ := hx.exists_orderOf_dvd_pow ⟨x, Subgroup.mem_zpowers x⟩
  rw [Subgroup.orderOf_mk] at hk
  have h1 : orderOf (QuotientGroup.mk' H x) ∣ 2 ^ k :=
    (orderOf_map_dvd (QuotientGroup.mk' H) x).trans hk
  have h2 : orderOf (QuotientGroup.mk' H x) ∣ H.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) H.index :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hone : orderOf (QuotientGroup.mk' H x) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp hone)

theorem mem_centralizerResidual_of_isPGroup_of_l34SuzOdd (hS : L34SuzOddSetting A t) {d : G}
    (hdA : d ∈ A) (hd : d * d = 1)
    (hperf : Group.IsPerfect ↥(centralizer ({QuotientGroup.mk' (center ↥A) ⟨d, hdA⟩} :
      Set (↥A ⧸ center ↥A))))
    {x : G} (hxA : x ∈ A) (hxd : x * d = d * x) (hx2 : IsPGroup 2 (zpowers x)) :
    x ∈ HarrisLit.centralizerResidual A d := by
  set S := ↥A ⧸ Subgroup.center ↥A with hSdef
  set π : ↥A →* S := QuotientGroup.mk' (Subgroup.center ↥A) with hπdef
  set dA : ↥A := ⟨d, hdA⟩ with hdAdef
  set Cg : Subgroup G := A ⊓ Subgroup.centralizer ({d} : Set G) with hCgdef
  set Hg : Subgroup S := Subgroup.centralizer ({π dA} : Set S) with hHgdef
  have hCgA : Cg ≤ A := inf_le_left
  have hdA2 : dA * dA = 1 := Subtype.ext (by simpa using hd)
  have hdP : IsPGroup 2 (Subgroup.zpowers dA) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hdA2))
  have hCmap : (Subgroup.centralizer ({dA} : Set ↥A)).map π = Hg := by
    simpa [π, dA, Hg, S, hdAdef] using
      CFSG.ClassicalInvolution.Balance.map_centralizer_singleton_eq
        (N := Subgroup.center ↥A) hS.odd_card_center hdP
  have hmem : ∀ z : ↥Cg, π (Subgroup.inclusion hCgA z) ∈ Hg := by
    intro z
    have hz : Subgroup.inclusion hCgA z ∈ Subgroup.centralizer ({dA} : Set ↥A) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp z.2.2)
    have := Subgroup.mem_map_of_mem π hz
    rwa [hCmap] at this
  let φ : ↥Cg →* ↥Hg := (π.comp (Subgroup.inclusion hCgA)).codRestrict Hg hmem
  have hφ : Function.Surjective φ := by
    intro y
    have hy : (y : S) ∈ (Subgroup.centralizer ({dA} : Set ↥A)).map π := by
      rw [hCmap]; exact y.2
    obtain ⟨c, hc, hcy⟩ := hy
    have hcd : (c : G) * d = d * (c : G) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)
    refine ⟨⟨c.1, ⟨c.2, ?_⟩⟩, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hcd
    · exact Subtype.ext hcy
  have hPmap : (perfectResidual ↥Cg).map φ = ⊤ := by
    have htop : CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥Hg = ⊤ := by
      simp [CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual]
    have h' := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq φ hφ
    rw [htop] at h'
    exact h'
  have hker_eq : φ.ker = (Subgroup.center ↥A).comap (Subgroup.inclusion hCgA) := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    constructor
    · intro h
      have h' : (φ c : S) = 1 := congrArg Subtype.val h
      rw [show (φ c : S) = π (Subgroup.inclusion hCgA c) from rfl] at h'
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hCgA c)).mp h'
    · intro h
      refine Subtype.ext ?_
      rw [show (φ c : S) = π (Subgroup.inclusion hCgA c) from rfl]
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hCgA c)).mpr h
  have hKodd : Odd (Nat.card φ.ker) := by
    rw [hker_eq]
    exact hS.odd_card_center.of_dvd_nat
      (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hCgA))
  have hsup : perfectResidual ↥Cg ⊔ φ.ker = ⊤ := by
    rw [eq_top_iff]
    intro c _
    have hc : φ c ∈ (perfectResidual ↥Cg).map φ := by rw [hPmap]; exact Subgroup.mem_top _
    obtain ⟨p, hp, hpc⟩ := hc
    have hmem : p⁻¹ * c ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpc, inv_mul_cancel]
    have hc_eq : c = p * (p⁻¹ * c) := by group
    rw [hc_eq]
    exact Subgroup.mul_mem_sup hp hmem
  have hPindex : Odd (perfectResidual ↥Cg).index := by
    have h1 : (perfectResidual ↥Cg).index = (perfectResidual ↥Cg).relIndex ⊤ :=
      (Subgroup.relIndex_top_right _).symm
    rw [h1, ← hsup, sup_comm, Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_right]
    exact hKodd.of_dvd_nat (Subgroup.relIndex_dvd_card _ _)
  have hxCg : x ∈ Cg := ⟨hxA, Subgroup.mem_centralizer_singleton_iff.mpr hxd⟩
  let xC : ↥Cg := ⟨x, hxCg⟩
  have hxC2 : IsPGroup 2 (Subgroup.zpowers xC) := by
    obtain ⟨k, hk⟩ := hx2.exists_orderOf_dvd_pow ⟨x, Subgroup.mem_zpowers x⟩
    rw [Subgroup.orderOf_mk] at hk
    exact IsPGroup.of_card_dvd_pow (n := k) (by
      rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
      exact hk)
  have hxP : xC ∈ perfectResidual ↥Cg := mem_of_isPGroup_of_odd_index hPindex hxC2
  change x ∈ (perfectResidual ↥Cg).map Cg.subtype
  exact Subgroup.mem_map.mpr ⟨xC, hxP, rfl⟩

theorem exists_mulAut_centralizer_of_l34SuzOdd (hS : L34SuzOddSetting A t) {d : G}
    (hdA : d ∈ A) (hd : d * d = 1)
    (hperf : Group.IsPerfect ↥(centralizer ({QuotientGroup.mk' (center ↥A) ⟨d, hdA⟩} :
      Set (↥A ⧸ center ↥A))))
    (hcen : ∀ z ∈ centralizer ({QuotientGroup.mk' (center ↥A) ⟨d, hdA⟩} : Set (↥A ⧸ center ↥A)),
      (∀ x ∈ centralizer ({QuotientGroup.mk' (center ↥A) ⟨d, hdA⟩} : Set (↥A ⧸ center ↥A)),
        z * x = x * z) → z = 1 ∨ z = QuotientGroup.mk' (center ↥A) ⟨d, hdA⟩)
    {g : G}
    (hg : (HarrisLit.centralizerResidual A d).map (MulAut.conj g).toMonoidHom =
      HarrisLit.centralizerResidual A d) :
    ∃ α : MulAut ↥(centralizer ({QuotientGroup.mk' (center ↥A) ⟨d, hdA⟩} :
        Set (↥A ⧸ center ↥A))),
      ∀ x y : ↥A, (x : G) ∈ HarrisLit.centralizerResidual A d → (y : G) = g * x * g⁻¹ →
        ∀ (hx : QuotientGroup.mk' (center ↥A) x ∈
            centralizer ({QuotientGroup.mk' (center ↥A) ⟨d, hdA⟩} : Set (↥A ⧸ center ↥A)))
          (hy : QuotientGroup.mk' (center ↥A) y ∈
            centralizer ({QuotientGroup.mk' (center ↥A) ⟨d, hdA⟩} : Set (↥A ⧸ center ↥A))),
          α ⟨QuotientGroup.mk' (center ↥A) x, hx⟩ = ⟨QuotientGroup.mk' (center ↥A) y, hy⟩ := by
  set S := ↥A ⧸ Subgroup.center ↥A with hSdef
  set π : ↥A →* S := QuotientGroup.mk' (Subgroup.center ↥A) with hπdef
  set dA : ↥A := ⟨d, hdA⟩ with hdAdef
  set Hg : Subgroup S := Subgroup.centralizer ({π dA} : Set S) with hHgdef
  set L : Subgroup G := HarrisLit.centralizerResidual A d with hLdef
  have hLle : L ≤ A ⊓ Subgroup.centralizer ({d} : Set G) := HarrisLit.centralizerResidual_le
  have hLA : L ≤ A := hLle.trans inf_le_left
  have hdA2 : dA * dA = 1 := Subtype.ext (by simpa using hd)
  have hL1 : (L.subgroupOf A).map π = Hg := by
    have h := map_centralizerResidual_eq_of_l34SuzOdd hS hdA hd hperf
    simpa [L, π, Hg, S, dA, hdAdef] using h
  have hmemφ : ∀ x : ↥L, π (Subgroup.inclusion hLA x) ∈ Hg := by
    intro x
    have hx : Subgroup.inclusion hLA x ∈ L.subgroupOf A := x.2
    have := Subgroup.mem_map_of_mem π hx
    rwa [hL1] at this
  let φ : ↥L →* ↥Hg := (π.comp (Subgroup.inclusion hLA)).codRestrict Hg hmemφ
  have hφ : Function.Surjective φ := by
    intro y
    have hy : (y : S) ∈ (L.subgroupOf A).map π := by rw [hL1]; exact y.2
    obtain ⟨a, ha, hay⟩ := hy
    refine ⟨⟨a.1, ha⟩, ?_⟩
    have haeq : Subgroup.inclusion hLA (⟨a.1, ha⟩ : ↥L) = a := Subtype.ext rfl
    refine Subtype.ext ?_
    show π (Subgroup.inclusion hLA (⟨a.1, ha⟩ : ↥L)) = (y : S)
    rw [haeq]
    exact hay
  let eH : ↥L ⧸ φ.ker ≃* ↥Hg := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have heH : ∀ z : ↥L, eH (QuotientGroup.mk' φ.ker z) = φ z := fun z => rfl
  let ψL : ↥L ≃* ↥L := ((MulAut.conj g).subgroupMap L).trans (MulEquiv.subgroupCongr hg)
  have hψ : ∀ x : ↥L, (ψL x : G) = g * (x : G) * g⁻¹ := by
    intro x
    calc (ψL x : G)
        = (((MulEquiv.subgroupMap (MulAut.conj g) L) x :
            ↥(L.map (MulAut.conj g).toMonoidHom)) : G) :=
          MulEquiv.subgroupCongr_apply hg ((MulEquiv.subgroupMap (MulAut.conj g) L) x)
      _ = (MulAut.conj g) x := MulEquiv.coe_subgroupMap_apply (MulAut.conj g) L x
      _ = g * (x : G) * g⁻¹ := MulAut.conj_apply g x
  have hord_eq : ∀ x : ↥L, orderOf (Subgroup.inclusion hLA x) = orderOf x := by
    intro x
    rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe x]
    rfl
  have hker_iff : ∀ x : ↥L, x ∈ φ.ker ↔ x ∈ Subgroup.center ↥L ∧ Odd (orderOf x) := by
    intro x
    constructor
    · intro hx
      have hx1 : π (Subgroup.inclusion hLA x) = 1 := by
        have h := congrArg (fun z : ↥Hg => (z : S)) hx
        simpa [φ] using h
      have hxZ : Subgroup.inclusion hLA x ∈ Subgroup.center ↥A :=
        (QuotientGroup.eq_one_iff (Subgroup.inclusion hLA x)).mp hx1
      have hcent : x ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        show (y : G) * (x : G) = (x : G) * (y : G)
        exact congrArg (fun z : ↥A => (z : G))
          (Subgroup.mem_center_iff.mp hxZ (Subgroup.inclusion hLA y))
      refine ⟨hcent, ?_⟩
      rw [← hord_eq x]
      exact hS.odd_card_center.of_dvd_nat
        (Subgroup.orderOf_dvd_natCard _ hxZ)
    · rintro ⟨hc, hodd⟩
      have hz : π (Subgroup.inclusion hLA x) ∈ Hg := hmemφ x
      have hcomm : ∀ w ∈ Hg, π (Subgroup.inclusion hLA x) * w = w * π (Subgroup.inclusion hLA x) := by
        intro w hw
        rw [← hL1] at hw
        obtain ⟨a, ha, rfl⟩ := hw
        have hx_comm := Subgroup.mem_center_iff.mp hc (⟨a.1, ha⟩ : ↥L)
        have hval : (Subgroup.inclusion hLA x) * a = a * Subgroup.inclusion hLA x :=
          Subtype.ext (congrArg Subtype.val hx_comm).symm
        calc π (Subgroup.inclusion hLA x) * π a
            = π (Subgroup.inclusion hLA x * a) := (map_mul π _ _).symm
          _ = π (a * Subgroup.inclusion hLA x) := by rw [hval]
          _ = π a * π (Subgroup.inclusion hLA x) := map_mul π _ _
      have hxZ : Subgroup.inclusion hLA x ∈ Subgroup.center ↥A := by
        rcases hcen (π (Subgroup.inclusion hLA x)) hz hcomm with h1 | h1
        · exact (QuotientGroup.eq_one_iff _).mp h1
        · have hodd' : Odd (orderOf (Subgroup.inclusion hLA x)) := by
            rw [hord_eq x]; exact hodd
          have hdvd2 : orderOf (π (Subgroup.inclusion hLA x)) ∣ 2 := by
            rw [h1]
            exact (orderOf_map_dvd π dA).trans
              (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hdA2))
          have hone : orderOf (π (Subgroup.inclusion hLA x)) = 1 :=
            Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hodd') hdvd2
              (orderOf_map_dvd π _)
          exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp hone)
      refine Subtype.ext ?_
      show π (Subgroup.inclusion hLA x) = 1
      exact (QuotientGroup.eq_one_iff _).mpr hxZ
  have hker_map : φ.ker.map ψL.toMonoidHom = φ.ker := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hker_iff] at hx ⊢
      refine ⟨?_, ?_⟩
      · rw [Subgroup.mem_center_iff]
        intro z
        obtain ⟨w, rfl⟩ := ψL.surjective z
        show ψL w * ψL x = ψL x * ψL w
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx.1 w]
      · show Odd (orderOf (ψL x))
        rw [MulEquiv.orderOf_eq]
        exact hx.2
    · intro hy
      refine ⟨ψL.symm y, ?_, ψL.apply_symm_apply y⟩
      rw [hker_iff] at hy ⊢
      refine ⟨?_, ?_⟩
      · rw [Subgroup.mem_center_iff]
        intro z
        obtain ⟨w, rfl⟩ := ψL.symm.surjective z
        show ψL.symm w * ψL.symm y = ψL.symm y * ψL.symm w
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hy.1 w]
      · show Odd (orderOf (ψL.symm y))
        rw [MulEquiv.orderOf_eq]
        exact hy.2
  let α : MulAut ↥Hg := eH.symm.trans ((QuotientGroup.congr φ.ker φ.ker ψL hker_map).trans eH)
  refine ⟨α, ?_⟩
  intro x y hxL hyEq hx hy
  let xL : ↥L := ⟨x, hxL⟩
  have hstep : α (eH (QuotientGroup.mk' φ.ker xL)) =
      eH (QuotientGroup.mk' φ.ker (ψL xL)) := by
    simp only [α, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    exact congrArg eH (QuotientGroup.congr_mk' φ.ker φ.ker ψL hker_map xL)
  have hleft : (⟨π x, hx⟩ : ↥Hg) = eH (QuotientGroup.mk' φ.ker xL) := by
    rw [heH]
    refine Subtype.ext ?_
    show π x = π (Subgroup.inclusion hLA xL)
    rw [show Subgroup.inclusion hLA xL = x from Subtype.ext rfl]
  have hright : eH (QuotientGroup.mk' φ.ker (ψL xL)) = (⟨π y, hy⟩ : ↥Hg) := by
    rw [heH]
    refine Subtype.ext ?_
    show π (Subgroup.inclusion hLA (ψL xL)) = π y
    have hval : (ψL xL : G) = y := by
      rw [hψ xL]
      exact hyEq.symm
    rw [show Subgroup.inclusion hLA (ψL xL) = ⟨(ψL xL : G), hLA (ψL xL).2⟩ from rfl]
    rw [show (⟨(ψL xL : G), hLA (ψL xL).2⟩ : ↥A) = y from Subtype.ext hval]
  rw [hleft, hstep, hright]

end CFSG.ComponentClassification.GrSLit.L34Sec5S
