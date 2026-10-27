module

public import CFSG.GH74.Uniqueness.SU.SU7Bar
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GH74.Uniqueness.SU.KInputs

public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG.Blueprint

namespace Gen

theorem normal_generalizedFitting (X : Type*) [Group X] : (CFSG.generalizedFitting X).Normal := by
  rw [CFSG.generalizedFitting_eq_componentClassification]
  exact CFSG.ComponentClassification.GeneralizedFitting.normal X

variable {G : Type*} [Group G]

theorem mem_normalizer_centralizer {U : Subgroup G} {n : G} (hn : n ∈ normalizer (U : Set G)) :
    n ∈ normalizer ((centralizer (U : Set G) : Subgroup G) : Set G) := by
  have key : ∀ n ∈ normalizer (U : Set G), ∀ h ∈ centralizer (U : Set G),
      n * h * n⁻¹ ∈ centralizer (U : Set G) := by
    intro n hn h hh
    rw [mem_centralizer_iff] at hh ⊢
    intro p hp
    have hp' : n⁻¹ * p * n ∈ U := by
      refine (mem_normalizer_iff.1 hn (n⁻¹ * p * n)).2 ?_
      have : n * (n⁻¹ * p * n) * n⁻¹ = p := by group
      rw [this]; exact hp
    have h1 := hh _ hp'
    calc p * (n * h * n⁻¹) = n * ((n⁻¹ * p * n) * h) * n⁻¹ := by group
      _ = n * (h * (n⁻¹ * p * n)) * n⁻¹ := by rw [h1]
      _ = n * h * n⁻¹ * p := by group
  rw [mem_normalizer_iff]
  intro h
  refine ⟨key n hn h, fun h2 => ?_⟩
  have := key n⁻¹ ((normalizer (U : Set G)).inv_mem hn) _ h2
  simpa [mul_assoc] using this

end Gen

namespace Claim

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}

theorem normalizer_le_M (hH : Hyp184 S U M) {E : Subgroup G} (hES : E ≤ (S : Subgroup G))
    (hE : Open.IsElemAbelian 2 E) (h2 : 2 ≤ Open.pRank 2 E)
    (h3 : 3 ≤ Open.pRank 2 (centralizer (E : Set G) ⊓ (S : Subgroup G))) :
    normalizer (E : Set G) ≤ M := by
  refine le_trans ?_ hH.gamma_le
  unfold gammaElem
  exact le_iSup_of_le E (le_iSup_of_le hES (le_iSup_of_le hE (le_iSup_of_le h2
    (le_iSup_of_le h3 le_rfl))))

theorem normalizer_le_M_of_isE (hH : Hyp184 S U M) {E F : Subgroup G} {n m : ℕ}
    (hES : E ≤ (S : Subgroup G)) (hE : IsE n E) (hn : 2 ≤ n)
    (hF : F ≤ centralizer (E : Set G) ⊓ (S : Subgroup G)) (hFE : IsE m F) (hm : 3 ≤ m) :
    normalizer (E : Set G) ≤ M :=
  normalizer_le_M hH hES hE.1 (hn.trans (SU1.le_pRank (by norm_num) le_rfl hE.1 hE.2))
    (hm.trans (SU1.le_pRank (by norm_num) hF hFE.1 hFE.2))

theorem isSylowOf_T (hH : Hyp184 S U M) :
    ABGLocalTools.IsSylowOf 2 (Tsub S U) (centralizer (U : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ABGLocalTools.IsSylowOf 2 (S : Subgroup G) ⊤ := by
    rw [ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, S.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S.not_dvd_index
  have hSN : (S : Subgroup G) ≤ normalizer (U : Set G) := hH.normal
  have h2 := h1.of_le hSN le_top
  have h3 := h2.inf_of_le_normalizer (N := centralizer (U : Set G))
    (Subgroup.centralizer_le_normalizer _) (fun n hn => Gen.mem_normalizer_centralizer hn)
  rw [inf_comm] at h3
  exact h3

omit [Finite G] in
theorem mem_barImage_iff {X : Subgroup G} {y : Mbar M} :
    y ∈ barImage M X ↔ ∃ m : ↥M, (m : G) ∈ X ∧ QuotientGroup.mk' (pPrimeCore 2 ↥M) m = y := by
  unfold barImage
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨m, hm, rfl⟩; exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩; exact ⟨m, hm, rfl⟩

omit [Finite G] in
theorem barImage_mono {X Y : Subgroup G} (h : X ≤ Y) : barImage M X ≤ barImage M Y := by
  intro y hy
  obtain ⟨m, hm, rfl⟩ := mem_barImage_iff.1 hy
  exact mem_barImage_iff.2 ⟨m, h hm, rfl⟩

theorem orderOf_proj_eq_two (M : Subgroup G) {y : G} (hyM : y ∈ M) (hy2 : y * y = 1)
    (hy1 : y ≠ 1) :
    orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨y, hyM⟩) = 2 := by
  have hsq : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨y, hyM⟩ *
      QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨y, hyM⟩ = 1 := by
    rw [← map_mul]
    have : (⟨y, hyM⟩ : ↥M) * ⟨y, hyM⟩ = 1 := Subtype.ext hy2
    rw [this, map_one]
  have hne : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨y, hyM⟩ ≠ 1 := by
    intro h
    have h1 : (⟨y, hyM⟩ : ↥M) ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).1 h
    have h2 := Subgroup.orderOf_dvd_natCard _ h1
    have hord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
    rw [Subgroup.orderOf_mk, hord] at h2
    have := Nat.odd_iff.1 (Bar.odd_pPrimeCore M)
    omega
  exact orderOf_eq_prime (by rw [pow_two]; exact hsq) hne

theorem xbar_not_mem (hKI3 : K.KI3) (hH : Hyp184 S U M) (hconf : Conf18H S M V x z)
    (hLie : LieModel ↥(generalizedFitting (Mbar M)) .PSL 3 2 2)
    (h9 : 9 ∣ Nat.card ↥(centralizer ({xbar M x hconf.x_mem} : Set (Mbar M)) ⊓
      generalizedFitting (Mbar M))) :
    xbar M x hconf.x_mem ∉ generalizedFitting (Mbar M) := by
  intro hxF
  have hGH : SU0.GHGroup (Mbar M) :=
    SU0.GHGroup.of_kgh_quotient hH.kgh hH.maximal.1 (pPrimeCore 2 ↥M)
  have hO : pPrimeCore 2 (Mbar M) = ⊥ := CFSG.GH74.GLS.pPrimeCore_quotient_eq_bot ↥M
  have hxord : orderOf (xbar M x hconf.x_mem) = 2 :=
    orderOf_proj_eq_two M hconf.x_mem (Base.x_mul_self hconf) (Base.x_ne_one hconf)
  obtain ⟨-, -, hsyl⟩ := hKI3 (Mbar M) hGH hO hLie _ hxF hxord
  obtain ⟨n, hn⟩ := hsyl.2.1.exists_card_eq
  rw [hn] at h9
  have hcop : Nat.Coprime 9 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
  have := Nat.Coprime.eq_one_of_dvd hcop h9
  omega

theorem isSylowOf_bar_S (hconf : Conf18H S M V x z) :
    ABGLocalTools.IsSylowOf 2 (barImage M (S : Subgroup G)) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, ?_, ?_⟩
  · exact (Bar.isPGroup_subgroupOf S.isPGroup' M).map _
  · rw [Subgroup.relIndex_top_right]
    intro hdvd
    apply S.not_dvd_index
    refine hdvd.trans ?_
    have h1 : (barImage M (S : Subgroup G)).index ∣ ((S : Subgroup G).subgroupOf M).index :=
      Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)
    exact h1.trans (Subgroup.relIndex_dvd_index_of_le hconf.S_le)

theorem proj_mem_normalizer (hKI3 : K.KI3) (hH : Hyp184 S U M) (hconf : Conf18H S M V x z)
    (hcl : Concl189 S U M x hconf.x_mem) {g : G} (hgM : g ∈ M) (hgz : g * z = z * g) :
    QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨g, hgM⟩ ∈
      normalizer ((barImage M (Tsub S U) : Subgroup (Mbar M)) : Set (Mbar M)) := by
  rcases hcl.case with ha | hb
  · obtain ⟨hLie, -, h9⟩ := ha
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hJ := Base.j2facts hH hconf hcl
    have hFn : (generalizedFitting (Mbar M)).Normal := Gen.normal_generalizedFitting _
    have hxF := xbar_not_mem hKI3 hH hconf hLie h9
    have hTle := hcl.T_le
    have hSyl_SF : ABGLocalTools.IsSylowOf 2
        (barImage M (S : Subgroup G) ⊓ generalizedFitting (Mbar M)) (generalizedFitting (Mbar M)) :=
      (isSylowOf_bar_S hconf).inf_of_le_normalizer le_top
        (by rw [Subgroup.normalizer_eq_top])
    have hxM := hconf.x_mem
    have hTM : Tsub S U ≤ M := Base.T_le_S.trans hconf.S_le
    have hSF : barImage M (S : Subgroup G) ⊓ generalizedFitting (Mbar M) =
        barImage M (Tsub S U) := by
      apply le_antisymm
      · rintro y ⟨hyS, hyF⟩
        obtain ⟨s, hsS, rfl⟩ := mem_barImage_iff.1 hyS
        rcases hJ.S_cover s hsS with hsT | hxsT
        · exact mem_barImage_iff.2 ⟨s, hsT, rfl⟩
        · exfalso
          apply hxF
          have hxsM : x * (s : G) ∈ M := M.mul_mem hxM s.2
          have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨x * (s : G), hxsM⟩ ∈
              barImage M (Tsub S U) := mem_barImage_iff.2 ⟨⟨x * (s : G), hxsM⟩, hxsT, rfl⟩
          have h2 := hTle h1
          have e : xbar M x hxM = QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨x * (s : G), hxsM⟩ *
              (QuotientGroup.mk' (pPrimeCore 2 ↥M) s)⁻¹ := by
            rw [← map_inv, ← map_mul]
            unfold xbar
            congr 1
            exact Subtype.ext (by simp)
          rw [e]
          exact (generalizedFitting (Mbar M)).mul_mem h2
            ((generalizedFitting (Mbar M)).inv_mem hyF)
      · exact le_inf (barImage_mono Base.T_le_S) hTle
    have hzU : z ∈ U := (Base.mem_Zc_iff hH hconf hcl z).1 hJ.z_mem
    have hzT : z ∈ Tsub S U := Base.U_le_T hH hconf hcl hzU
    have hzM : z ∈ M := hTM hzT
    have hz2 := Base.z_mul_self hconf
    obtain ⟨zb, hzb⟩ : ∃ zb : Mbar M, zb = QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨z, hzM⟩ :=
      ⟨_, rfl⟩
    obtain ⟨gb, hgb⟩ : ∃ gb : Mbar M, gb = QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨g, hgM⟩ :=
      ⟨_, rfl⟩
    have hzF : zb ∈ generalizedFitting (Mbar M) := by
      rw [hzb]; exact hTle (mem_barImage_iff.2 ⟨⟨z, hzM⟩, hzT, rfl⟩)
    have hzord : orderOf zb = 2 := by
      rw [hzb]; exact orderOf_proj_eq_two M hzM hz2 (Base.z_ne_one hconf)
    have hGH : SU0.GHGroup (Mbar M) :=
      SU0.GHGroup.of_kgh_quotient hH.kgh hH.maximal.1 (pPrimeCore 2 ↥M)
    have hO : pPrimeCore 2 (Mbar M) = ⊥ := CFSG.GH74.GLS.pPrimeCore_quotient_eq_bot ↥M
    obtain ⟨-, -, hsyl⟩ := hKI3 (Mbar M) hGH hO hLie zb hzF hzord
    have hP₁ : ABGLocalTools.IsSylowOf 2
        (centralizer ({zb} : Set (Mbar M)) ⊓ generalizedFitting (Mbar M))
        (generalizedFitting (Mbar M)) := by
      rw [ABGLocalTools.isSylowOf_iff]
      obtain ⟨h1, h2, h3⟩ := hsyl
      exact ⟨h1, h2, by have := Nat.odd_iff.1 h3; omega⟩
    have hcard : Nat.card ↥(centralizer ({zb} : Set (Mbar M)) ⊓ generalizedFitting (Mbar M)) =
        Nat.card ↥(barImage M (Tsub S U)) := by
      rw [hP₁.card_eq, ← hSF, hSyl_SF.card_eq]
    have hTP : barImage M (Tsub S U) ≤
        centralizer ({zb} : Set (Mbar M)) ⊓ generalizedFitting (Mbar M) := by
      refine le_inf ?_ hTle
      intro y hy
      obtain ⟨t, htT, rfl⟩ := mem_barImage_iff.1 hy
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw, hzb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext ((mem_Zc.1 hJ.z_mem).2 t htT)
    have hEq := Subgroup.eq_of_le_of_card_ge hTP (hcard ▸ le_rfl)
    have hgz' : gb * zb = zb * gb := by
      rw [hgb, hzb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hgz
    rw [← hgb]
    apply Gen.mem_normalizer_of_conj_le
    intro y hy
    rw [hEq] at hy ⊢
    refine Subgroup.mem_inf.2 ⟨?_, hFn.conj_mem _ (Subgroup.mem_inf.1 hy).2 _⟩
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have hyc := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).1 _ (Set.mem_singleton _)
    calc zb * (gb * y * gb⁻¹) = (zb * gb) * y * gb⁻¹ := by group
      _ = (gb * zb) * y * gb⁻¹ := by rw [← hgz']
      _ = gb * (zb * y) * gb⁻¹ := by group
      _ = gb * (y * zb) * gb⁻¹ := by rw [hyc]
      _ = (gb * y * gb⁻¹) * (gb * zb * gb⁻¹) := by group
      _ = (gb * y * gb⁻¹) * zb := by rw [hgz']; group
  · rw [hb]
    have hFn : (generalizedFitting (Mbar M)).Normal := Gen.normal_generalizedFitting _
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _

theorem conj_mem_U (hKI3 : K.KI3) (hH : Hyp184 S U M) (hconf : Conf18H S M V x z)
    (hcl : Concl189 S U M x hconf.x_mem) {g : G} (hgM : g ∈ M) (hgz : g * z = z * g) {a u : G}
    (haT : a ∈ Tsub S U) (huU : u ∈ U) (hau : g⁻¹ * a * g = u) : a ∈ U := by
  have hTM : Tsub S U ≤ M := Base.T_le_S.trans hconf.S_le
  have hTp : IsPGroup 2 ↥(Tsub S U) := S.isPGroup'.to_le Base.T_le_S
  obtain ⟨n, hnM, hnN, hnπ⟩ := Bar.normalizer_lift hTp hTM hgM
    (proj_mem_normalizer hKI3 hH hconf hcl hgM hgz)
  have hmemZ := Base.mem_Zc_iff hH hconf hcl
  have huT : u ∈ Tsub S U := Base.U_le_T hH hconf hcl huU
  have hnuU : n * u * n⁻¹ ∈ U :=
    (hmemZ _).1 (Base.mem_Zc_of_normalizer hnN ((hmemZ u).2 huU))
  have hnuT : n * u * n⁻¹ ∈ Tsub S U := (mem_normalizer_iff.1 hnN u).1 huT
  have hau' : a = g * u * g⁻¹ := by rw [← hau]; group
  have hga : (⟨a, hTM haT⟩ : ↥M) = ⟨g, hgM⟩ * ⟨u, hTM huT⟩ * ⟨g, hgM⟩⁻¹ := Subtype.ext hau'
  have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨a, hTM haT⟩ =
      QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨n * u * n⁻¹, hTM hnuT⟩ := by
    have e : (⟨n * u * n⁻¹, hTM hnuT⟩ : ↥M) = ⟨n, hnM⟩ * ⟨u, hTM huT⟩ * ⟨n, hnM⟩⁻¹ := rfl
    rw [hga, e, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hnπ]
  have h2 := Bar.eq_of_proj_eq hTp hTM haT hnuT h1
  rw [h2]
  exact hnuU

theorem claim_A (hKI3 : K.KI3) (hH : Hyp184 S U M) (hconf : Conf18H S M V x z)
    (hcl : Concl189 S U M x hconf.x_mem) {A B : Subgroup G}
    (hL : L34Facts (Tsub S U) A B) (hAx : A.map (MulAut.conj x).toMonoidHom = B) {a u g₀ : G}
    (haA : a ∈ A) (hg₀z : g₀ * z = z * g₀) (hg₀ : g₀⁻¹ * a * g₀ = u)
    (huU : u ∈ U) (hu1 : u ≠ 1) (huz : u ≠ z) : a ∈ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ := Base.j2facts hH hconf hcl
  have hxS := Base.x_mem_S hconf
  have hxM : x ∈ M := hconf.x_mem
  have hzU : z ∈ U := (Base.mem_Zc_iff hH hconf hcl z).1 hJ.z_mem
  have hz1 := Base.z_ne_one hconf
  have hzz := Base.z_mul_self hconf
  have hUc : ∀ p ∈ U, ∀ q ∈ U, p * q = q * p := (isElemAbelian_iff.1 hH.four.2.1).1
  have hU4 : Nat.card U = 4 := by rw [hH.four.2.2]; norm_num
  have hall := Gen.eq_four_of_card hU4 hzU huU hz1 hu1 huz hzz (hUc z hzU u huU)
  have hAab := (isElemAbelian_iff.1 hL.A_E.1)
  have haT : a ∈ Tsub S U := hL.A_le haA
  set K' : Subgroup G := ((S : Subgroup G) ⊓ centralizer ({a} : Set G)).map
    (MulAut.conj g₀⁻¹).toMonoidHom with hK'
  have hKcentU : K' ≤ centralizer (U : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨hcS, hca⟩ := Subgroup.mem_inf.1 hc
    have hac : a * c = c * a := mem_centralizer_iff.1 hca a (Set.mem_singleton a)
    have hcz : c * z = z * c := hconf.z_center c hcS
    have e : (MulAut.conj g₀⁻¹).toMonoidHom c = g₀⁻¹ * c * g₀ := by
      simp
    rw [e, mem_centralizer_iff]
    intro p hp
    have h1 : Commute z g₀ := hg₀z.symm
    have h2 : Commute z c := hcz.symm
    have hzc : Commute z (g₀⁻¹ * c * g₀) := ((h1.inv_right).mul_right h2).mul_right h1
    have huc : Commute u (g₀⁻¹ * c * g₀) := by
      show u * (g₀⁻¹ * c * g₀) = (g₀⁻¹ * c * g₀) * u
      rw [← hg₀]
      calc g₀⁻¹ * a * g₀ * (g₀⁻¹ * c * g₀) = g₀⁻¹ * (a * c) * g₀ := by group
        _ = g₀⁻¹ * (c * a) * g₀ := by rw [hac]
        _ = g₀⁻¹ * c * g₀ * (g₀⁻¹ * a * g₀) := by group
    rcases hall p hp with h | h | h | h
    · rw [h]; simp
    · rw [h]; exact hzc.eq
    · rw [h]; exact huc.eq
    · rw [h]; exact (hzc.mul_left huc).eq
  have hsyl := ABGLocalTools.isSylowOf_iff.1 (isSylowOf_T hH)
  have hKp : IsPGroup 2 ↥K' := (S.isPGroup'.to_le inf_le_left).map _
  obtain ⟨c₀, hc₀, hc₀K⟩ := CFSG.GH74.GLS.Bg.Thompson.exists_conj_into_sylow (p := 2) hKcentU hKp
    hsyl.1 hsyl.2.1 hsyl.2.2
  set g := g₀ * c₀ with hg
  have hc₀z : z * c₀ = c₀ * z := mem_centralizer_iff.1 hc₀ z hzU
  have hc₀u : u * c₀ = c₀ * u := mem_centralizer_iff.1 hc₀ u huU
  have hgz : g * z = z * g := by
    calc g₀ * c₀ * z = g₀ * (c₀ * z) := by group
      _ = g₀ * (z * c₀) := by rw [hc₀z]
      _ = (g₀ * z) * c₀ := by group
      _ = (z * g₀) * c₀ := by rw [hg₀z]
      _ = z * (g₀ * c₀) := by group
  have hgu : g⁻¹ * a * g = u := by
    have : g⁻¹ * a * g = c₀⁻¹ * (g₀⁻¹ * a * g₀) * c₀ := by rw [hg]; group
    rw [this, hg₀]
    calc c₀⁻¹ * u * c₀ = c₀⁻¹ * (u * c₀) := by group
      _ = c₀⁻¹ * (c₀ * u) := by rw [hc₀u]
      _ = u := by group
  have hgy : ∀ y ∈ (S : Subgroup G) ⊓ centralizer ({a} : Set G), g⁻¹ * y * g ∈ Tsub S U := by
    intro y hy
    have := hc₀K (g₀⁻¹ * y * g₀) ⟨y, hy, by simp⟩
    have e : g⁻¹ * y * g = c₀⁻¹ * (g₀⁻¹ * y * g₀) * c₀ := by rw [hg]; group
    rw [e]; exact this
  have hAcS : A ≤ centralizer (A : Set G) ⊓ (S : Subgroup G) := by
    intro y hy
    refine Subgroup.mem_inf.2 ⟨?_, Base.T_le_S (hL.A_le hy)⟩
    rw [mem_centralizer_iff]
    intro w hw
    exact hAab.1 w hw y hy
  have hAS : A ≤ (S : Subgroup G) ⊓ centralizer ({a} : Set G) := by
    intro y hy
    refine Subgroup.mem_inf.2 ⟨Base.T_le_S (hL.A_le hy), ?_⟩
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact hAab.1 a haA y hy
  have hNA : normalizer (A : Set G) ≤ M :=
    normalizer_le_M_of_isE hH (Base.T_le_S.trans' hL.A_le) hL.A_E (by norm_num) hAcS hL.A_E
      (by norm_num)
  set Ag : Subgroup G := A.map (MulAut.conj g⁻¹).toMonoidHom with hAg
  have hAgT : Ag ≤ Tsub S U := by
    rintro _ ⟨y, hy, rfl⟩
    have := hgy y (hAS hy)
    simpa [MulAut.conj_apply] using this
  have hAgE : IsE 4 Ag := (isE_map (MulAut.conj g⁻¹).injective).2 hL.A_E
  have hgM : g ∈ M := by
    rcases hL.unique Ag hAgT hAgE with hAA | hAB
    · have hcl' : ∀ y ∈ A, g * y * g⁻¹ ∈ A := by
        intro y hy
        have hyAg : y ∈ Ag := by rw [hAA]; exact hy
        obtain ⟨y', hy', hyy'⟩ := hyAg
        have : g * y * g⁻¹ = y' := by
          rw [← hyy']; simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
        rw [this]; exact hy'
      exact hNA (Gen.mem_normalizer_of_conj_le hcl')
    · have hcl' : ∀ y ∈ A, (g * x)⁻¹ * y * ((g * x)⁻¹)⁻¹ ∈ A := by
        intro y hy
        have hyAg : g⁻¹ * y * g ∈ Ag := ⟨y, hy, by simp⟩
        rw [hAB, ← hAx] at hyAg
        obtain ⟨a', ha', hxa'⟩ := hyAg
        have : (g * x)⁻¹ * y * ((g * x)⁻¹)⁻¹ = a' := by
          have h1 : x * a' * x⁻¹ = g⁻¹ * y * g := by
            simpa [MulAut.conj_apply] using hxa'
          have h2 : a' = x⁻¹ * (g⁻¹ * y * g) * x := by rw [← h1]; group
          rw [h2]; group
        rw [this]; exact ha'
      have hgxN : (g * x)⁻¹ ∈ normalizer (A : Set G) := Gen.mem_normalizer_of_conj_le hcl'
      have hgxN' : g * x ∈ normalizer (A : Set G) := by
        simpa using (normalizer (A : Set G)).inv_mem hgxN
      have hgxM : g * x ∈ M := hNA hgxN'
      have : g = (g * x) * x⁻¹ := by group
      rw [this]
      exact M.mul_mem hgxM (M.inv_mem hxM)
  exact conj_mem_U hKI3 hH hconf hcl hgM hgz haT huU hgu

theorem claim (hKI3 : K.KI3) (hH : Hyp184 S U M) (hconf : Conf18H S M V x z)
    (hcl : Concl189 S U M x hconf.x_mem) {a u g₀ : G} (haT : a ∈ Tsub S U) (ha2 : a * a = 1)
    (hg₀z : g₀ * z = z * g₀) (hg₀ : g₀⁻¹ * a * g₀ = u) (huU : u ∈ U) (hu1 : u ≠ 1)
    (huz : u ≠ z) : a ∈ U := by
  have hJ := Base.j2facts hH hconf hcl
  obtain ⟨A, B, hL, hAx, -, -, -, -⟩ := hJ.AB
  have hxS := Base.x_mem_S hconf
  have hxx := Base.x_mul_self hconf
  have ha1 : a ≠ 1 := by
    intro h
    rw [h] at hg₀
    apply hu1
    rw [← hg₀]; group
  rcases hL.invol a haT ha1 (by rw [pow_two]; exact ha2) with haA | haB
  · exact claim_A hKI3 hH hconf hcl hL hAx haA hg₀z hg₀ huU hu1 huz
  · rw [← hAx] at haB
    obtain ⟨a₁, ha₁, hxa₁⟩ := haB
    have hxa₁' : x * a₁ * x⁻¹ = a := by simpa [MulAut.conj_apply] using hxa₁
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    have ha₁eq : a₁ = x * a * x⁻¹ := by
      rw [← hxa₁', hxinv]
      calc a₁ = (x * x) * a₁ * (x * x) := by rw [hxx]; group
        _ = x * (x * a₁ * x) * x := by group
    have hg₀' : (x * g₀)⁻¹ * a₁ * (x * g₀) = u := by
      rw [ha₁eq, ← hg₀]; group
    have hg₀'z : (x * g₀) * z = z * (x * g₀) := by
      calc x * g₀ * z = x * (g₀ * z) := by group
        _ = x * (z * g₀) := by rw [hg₀z]
        _ = (x * z) * g₀ := by group
        _ = (z * x) * g₀ := by rw [hconf.z_center x hxS]
        _ = z * (x * g₀) := by group
    have ha₁U := claim_A hKI3 hH hconf hcl hL hAx ha₁ hg₀'z hg₀' huU hu1 huz
    have := Base.U_norm hH x hxS a₁ ha₁U
    rw [← hxa₁']
    exact this

end Claim

end CFSG.GH74.Uniqueness.SU.SU7
