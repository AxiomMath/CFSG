module

public import CFSG.Quasithin.H13.A5S136sz2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136ab3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136abR
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5X1367d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Assembly.LowTwoRank
open CFSG.Blueprint CFSG.SectionRank

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem compFacts_of_isSz_F4
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) {K : Subgroup G}
    (hK : IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G))) {n : ℕ} (hSz : IsSz n ↥K) :
    SzPair.CompFacts S.Tv K := by
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hT2 : IsPGroup 2 S.Tv := (S.isSylowTwoOf_Tv_F4 h1222 h517).2.1
  have hKN : K ≤ Gv ⊓ Subgroup.normalizer (K : Set G) := le_inf hK.1 Subgroup.le_normalizer
  have hsyl : IsSylowTwoOf (S.Tv ⊓ K) K := by
    have h1 := A4.isSylowTwoOf_inf_normal (S.isSylowTwoOf_Tv_inf_F4 h1222 h517 h37 h38 hK) hKN
      inf_le_right
    rwa [inf_assoc, inf_eq_right.mpr hKN] at h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 ((S.Tv ⊓ K).subgroupOf K) :=
    hsyl.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.le).symm
  let P : Sylow 2 ↥K := hS2.toSylow hsyl.2.2
  have hP : ∀ x : ↥K, x ∈ (P : Subgroup ↥K) ↔ (x : G) ∈ S.Tv ⊓ K := fun x => Iff.rfl
  have hqs : CFSG.IsQuasisimple ↥K :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hK.1)).1 hK.2.1
  have hZ := ConfAB.center_eq_bot_of_simple hqs (ConfSz.isSimpleGroup hSz)
  refine ⟨hsyl, ?_, ?_, ?_, ?_⟩
  · intro x hx hc
    have hxZ : (⟨x, hx⟩ : ↥K) ∈ Subgroup.center ↥K :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2).symm
    rw [hZ, Subgroup.mem_bot] at hxZ
    exact congrArg Subtype.val hxZ
  · intro s hs hsN
    obtain ⟨m, hm⟩ := hT2 ⟨s, hs⟩
    have hsm : s ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hα : K.normalizerMonoidHom ⟨s, hsN⟩ ^ 2 ^ m = 1 := by
      rw [← map_pow]
      have : (⟨s, hsN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 ^ m = 1 :=
        Subtype.ext (by simpa using hsm)
      rw [this, map_one]
    obtain ⟨g, hg⟩ := ConfSz.exists_conj_of_two_pow hSz _ hα
    refine ⟨g, g.2, fun x hx => ?_⟩
    have := congrArg Subtype.val (DFunLike.congr_fun hg ⟨x, hx⟩)
    simpa [MulAut.conj_apply] using this
  · intro x hx hx2 y hy
    have := ConfSz.comm_of_sq_eq_one hSz P (x := ⟨x, hx.2⟩) (y := ⟨y, hy.2⟩) ((hP _).2 hx)
      (Subtype.ext (by simpa using hx2)) ((hP _).2 hy)
    exact congrArg Subtype.val this
  · obtain ⟨x, hx, y, hy, hx2, hy2, hx1, hy1, hxy⟩ := ConfSz.exists_two_involutions hSz P
    refine ⟨x, (hP x).1 hx, y, (hP y).1 hy, ?_, ?_, fun h => hx1 (Subtype.ext h),
      fun h => hy1 (Subtype.ext h), fun h => hxy (Subtype.ext h)⟩
    · simpa using congrArg Subtype.val hx2
    · simpa using congrArg Subtype.val hy2

theorem comm_mem_of_odd_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) {K K₁ : Subgroup G}
    (hK : K ≤ Subgroup.centralizer ({S.v12} : Set G)) (hPair : SzPair.PairFacts S.Tv K K₁)
    (hCK : SzPair.CompFacts S.Tv K) (hCK₁ : SzPair.CompFacts S.Tv K₁) (hT2 : IsPGroup 2 S.Tv)
    (h3 : ¬ 3 ∣ Nat.card K) {y : G} (hy : y ∈ S.Lv) (hyN : y ∈ Subgroup.normalizer (K : Set G))
    {b : G} (hbK : b ∈ K) (hbN : b ∈ Subgroup.normalizer ((S.Tv ⊓ K : Subgroup G) : Set G))
    (hodd : Odd (orderOf b)) : y * b * y⁻¹ * b⁻¹ ∈ S.Tv ⊓ K := by
  have hbB : b ∈ Subgroup.normalizer (baum T : Set G) := by
    have := SzPair.mem_normalizer_baum hPair hCK hCK₁ hT2 hbK hbN
    rwa [show baum S.Tv = baum T from S.lemma_13_6_4.1] at this
  obtain ⟨hbV, hbv⟩ := Subgroup.mem_inf.mp
    (S.lemma_13_6_5_F4 h1222 h517 (Subgroup.mem_inf.mpr ⟨hK hbK, hbB⟩))
  have hfix : pact (S.frame.ρ ⟨b, hbV⟩) E12 = E12 := by
    have h1 : b * S.v12 * b⁻¹ = S.v12 := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hbv
      rw [hbv]
      group
    have h2 := (S.conj_eq_iff ⟨b, hbV⟩ ⟨S.v12, S.v12_mem_V⟩).1 h1
    rwa [S.psi_v12] at h2
  have h6 : S.frame.ρ ⟨b, hbV⟩ ^ 6 = 1 := perm_fix_E12_pow_six _ hfix
  have hm : S.frame.ρ ⟨b, hbV⟩ ^ orderOf b = 1 := by
    rw [← map_pow]
    have : (⟨b, hbV⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ orderOf b = 1 :=
      Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, map_one]
  have h3b : ¬ 3 ∣ orderOf b := by
    intro h
    apply h3
    rw [← Subgroup.orderOf_mk b hbK] at h
    exact h.trans (orderOf_dvd_natCard _)
  have hcop : Nat.Coprime 6 (orderOf b) := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.coprime_mul_iff_left]
    exact ⟨Nat.coprime_two_left.mpr hodd,
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3b⟩
  have hρ : S.frame.ρ ⟨b, hbV⟩ = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one h6
    have h2 := orderOf_dvd_of_pow_eq_one hm
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)
  have hbC := S.frame.mem_centralizer_of_rho ⟨b, hbV⟩ hρ
  have hc := S.comm_mem_cLT hy hbV hbC
  have hcK : y * b * y⁻¹ * b⁻¹ ∈ K :=
    K.mul_mem (SzPair.conj_mem_of_mem_normalizer hyN hbK) (K.inv_mem hbK)
  have hR : K ⊓ ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) ≤ S.Tv ⊓ K := by
    refine ConfSz.le_of_isPGroup hCK.syl inf_le_left ?_ fun s hs => ?_
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h1 : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
        rw [S.cLT]
        exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)
      exact h1.to_le inf_le_right
    · obtain ⟨hsTv, hsK⟩ := Subgroup.mem_inf.mp hs
      have hsT : s ∈ T := (Subgroup.mem_inf.mp hsTv).1
      exact ConfSz.mem_normalizer_inf (Subgroup.le_normalizer hsK)
        (ConfSz.mem_normalizer_inf (Subgroup.le_normalizer (Subgroup.mem_sup_right hsT))
          (ConfSz.mem_normalizer_centralizer (S.frame.T_le hsT)))
  exact hR (Subgroup.mem_inf.mpr ⟨hcK, hc⟩)

theorem comm_mem_of_mem_normalizer_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) {K K₁ : Subgroup G}
    (hK : K ≤ Subgroup.centralizer ({S.v12} : Set G)) (hPair : SzPair.PairFacts S.Tv K K₁)
    (hCK : SzPair.CompFacts S.Tv K) (hCK₁ : SzPair.CompFacts S.Tv K₁) (hT2 : IsPGroup 2 S.Tv)
    (h3 : ¬ 3 ∣ Nat.card K) {y : G} (hy : y ∈ S.Lv) (hyN : y ∈ Subgroup.normalizer (K : Set G))
    {b : G} (hbK : b ∈ K) (hbN : b ∈ Subgroup.normalizer ((S.Tv ⊓ K : Subgroup G) : Set G)) :
    y * b * y⁻¹ * b⁻¹ ∈ S.Tv ⊓ K := by
  set P := S.Tv ⊓ K with hP
  have hyP := S.mem_normalizer_Tv_inf hCK.syl h3 hy hyN
  let H₀ : Subgroup G :=
    { carrier := {x | x ∈ Subgroup.normalizer (P : Set G) ∧ y * x * y⁻¹ * x⁻¹ ∈ P}
      mul_mem' := fun {a c} ha hc => by
        refine ⟨Subgroup.mul_mem _ ha.1 hc.1, ?_⟩
        have h1 := P.mul_mem ha.2 (SzPair.conj_mem_of_mem_normalizer ha.1 hc.2)
        rw [show y * a * y⁻¹ * a⁻¹ * (a * (y * c * y⁻¹ * c⁻¹) * a⁻¹) =
          y * (a * c) * y⁻¹ * (a * c)⁻¹ by group] at h1
        exact h1
      one_mem' := ⟨Subgroup.one_mem _, by simp [P.one_mem]⟩
      inv_mem' := fun {a} ha => by
        refine ⟨Subgroup.inv_mem _ ha.1, ?_⟩
        have h1 := SzPair.conj_inv_mem_of_mem_normalizer ha.1 (P.inv_mem ha.2)
        rw [show a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a = y * a⁻¹ * y⁻¹ * a⁻¹⁻¹ by group] at h1
        exact h1 }
  have hb : b ∈ H₀ := by
    refine ConfSz.mem_of_parts (fun x hx hxo => ?_) (fun x hx k hk => ?_)
    · have hxK : x ∈ K := (Subgroup.zpowers_le.mpr hbK) hx
      have hxN : x ∈ Subgroup.normalizer (P : Set G) := (Subgroup.zpowers_le.mpr hbN) hx
      exact ⟨hxN, S.comm_mem_of_odd_F4 h1222 h517 hK hPair hCK hCK₁ hT2 h3 hy hyN hxK hxN hxo⟩
    · have hxK : x ∈ K := (Subgroup.zpowers_le.mpr hbK) hx
      have hxN : x ∈ Subgroup.normalizer (P : Set G) := (Subgroup.zpowers_le.mpr hbN) hx
      have hxP : x ∈ P := ConfSz.mem_of_two_pow hCK.syl hxK hxN hk
      exact ⟨hxN, P.mul_mem (SzPair.conj_mem_of_mem_normalizer hyP hxP) (P.inv_mem hxP)⟩
  exact hb.2

end Setting

theorem elim1366SzPair_of_F4
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) : Elim1366SzPair_F4 := by
  intro G _ _ T L V S _ K hK hnn hSzK hinner
  obtain ⟨n, hSz⟩ := hSzK
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hTv := S.isSylowTwoOf_Tv_F4 h1222 h517
  have hT2 : IsPGroup 2 S.Tv := hTv.2.1
  have : IsSimpleGroup G := S.h13.simple
  have hKc : K ∈ cComp Gv := by
    have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hK.1] at h2
  have hcore := qtkeCore_of_cat S.h13.nonabelian S.h13.qtke
  have hcard : (conjSubgroupsBy Gv K).ncard = 2 :=
    ((Vol2Native.lemma_1_2_1_three hcore.1 h37 h38 S.pCoreOf_Gv_ne_bot' hKc).resolve_left hnn).1
  obtain ⟨t, htT, htN⟩ := exists_not_mem_normalizer_of_ncard_two hTv hcard
  have htG : t ∈ Gv := S.Tv_le_Gv htT
  set K₁ := K.map (MulAut.conj t).toMonoidHom with hK₁def
  have hne : K ≠ K₁ := fun h => htN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)

  have hKcomp : CFSG.Assembly.IsComponentOf K Gv :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hK.1).2 hK.2
  have hGt : Gv.map (MulAut.conj t).toMonoidHom = Gv :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htG)
  have hK₁comp : CFSG.Assembly.IsComponentOf K₁ Gv := by
    have := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hKcomp t
    rwa [hGt] at this
  have hK₁ : IsComponentIn K₁ Gv :=
    ⟨hK₁comp.1,
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
        hK₁comp.1).1 hK₁comp⟩
  have hSz₁ : IsSz n ↥K₁ :=
    suzukiModel_of_mulEquiv (K.equivMapOfInjective _ (MulAut.conj t).injective).symm hSz
  have hcomm : ∀ x ∈ K, ∀ y ∈ K₁, x * y = y * x := by
    rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hKcomp hK₁comp
      with h | h
    · exact absurd h hne
    · intro x hx y hy
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx
      exact (Subgroup.mem_centralizer_iff.mp this y hy).symm

  have hmem : ∀ s ∈ S.Tv, K.map (MulAut.conj s).toMonoidHom ∈ conjSubgroupsBy Gv K :=
    fun s hs => ⟨s, S.Tv_le_Gv hs, rfl⟩
  have hKmem : K ∈ conjSubgroupsBy Gv K := ⟨1, Gv.one_mem, by ext x; simp⟩
  have hK₁mem : K₁ ∈ conjSubgroupsBy Gv K := ⟨t, htG, rfl⟩
  have key : ∀ (M : Subgroup G) (s x : G),
      x ∈ M ↔ s * x * s⁻¹ ∈ M.map (MulAut.conj s).toMonoidHom := fun M s x => by
    rw [ConfSz.mem_map_conj]
    simp [mul_assoc]
  have hPair : SzPair.PairFacts S.Tv K K₁ := by
    refine ⟨hne, hcomm, fun s hs hsN x => ?_, fun s hs hsN x => ?_⟩
    · have hX := (ConfSz.eq_or_eq_of_ncard_two hcard hKmem hK₁mem hne (hmem s hs)).resolve_left
        fun h => hsN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
      rw [← hX]
      exact key K s x
    · have hX1 : K₁.map (MulAut.conj s).toMonoidHom ∈ conjSubgroupsBy Gv K :=
        ⟨s * t, Gv.mul_mem (S.Tv_le_Gv hs) htG, (ConfSz.map_conj_mul K s t).symm⟩
      have hX := (ConfSz.eq_or_eq_of_ncard_two hcard hKmem hK₁mem hne hX1).resolve_right
        fun h => hsN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
      rw [← hX]
      exact key K₁ s x
  have hCK := S.compFacts_of_isSz_F4 h1222 h517 h37 h38 hK hSz
  have hCK₁ := S.compFacts_of_isSz_F4 h1222 h517 h37 h38 hK₁ hSz₁

  obtain ⟨X, Q, y, hyLv, hconf⟩ := S.exists_conf1366_Lv_F4 h1222 h517 h37 h38 hK hinner
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := hconf.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hyodd : Odd (orderOf y) := hconf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hyz := hconf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hy3 : y ^ 3 = 1 := S.pow_three_eq_one_of_mem_Lv hyLv hyodd
  have h3 := ConfSz.three_not_dvd_card hSz

  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 ((S.Tv ⊓ K).subgroupOf K) :=
    hCK.syl.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hCK.syl.le).symm
  let P : Sylow 2 ↥K := hS2.toSylow hCK.syl.2.2
  have hP : ∀ x : ↥K, x ∈ (P : Subgroup ↥K) ↔ (x : G) ∈ S.Tv ⊓ K := fun x => Iff.rfl
  set α := K.normalizerMonoidHom ⟨y, hyN⟩ with hα
  have hαapp : ∀ x : ↥K, ((α x : ↥K) : G) = y * x * y⁻¹ := fun _ => rfl
  have hyP := S.mem_normalizer_Tv_inf hCK.syl h3 hyLv hyN
  have hα1 : α = 1 := by
    refine KGSz.szCent_holds ↥K n hSz α ⟨1, ?_⟩ P (fun s hs => ?_) (fun b hb => ?_)
    · rw [pow_one, hα, ← map_pow]
      have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hy3)
      rw [this, map_one]
    · rw [hP, hαapp]
      exact SzPair.conj_mem_of_mem_normalizer hyP ((hP s).1 hs)
    · have hbN : (b : G) ∈ Subgroup.normalizer ((S.Tv ⊓ K : Subgroup G) : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        by_cases hx : x ∈ K
        · have h1 := (Subgroup.mem_normalizer_iff.mp hb) ⟨x, hx⟩
          rw [hP, hP] at h1
          exact h1
        · have h1 : x ∉ S.Tv ⊓ K := fun h => hx (Subgroup.mem_inf.mp h).2
          have h2 : (b : G) * x * (b : G)⁻¹ ∉ S.Tv ⊓ K := fun h => hx (by
            have := SzPair.conj_inv_mem_of_mem_normalizer (Subgroup.le_normalizer b.2)
              (Subgroup.mem_inf.mp h).2
            simpa [mul_assoc] using this)
          exact iff_of_false h1 h2
      rw [hP]
      show y * (b : G) * y⁻¹ * (b : G)⁻¹ ∈ S.Tv ⊓ K
      exact S.comm_mem_of_mem_normalizer_F4 h1222 h517 hK.1 hPair hCK hCK₁ hT2 h3 hyLv hyN b.2 hbN
  have hyc : ∀ x ∈ K, y * x * y⁻¹ = x := by
    intro x hx
    have := hαapp ⟨x, hx⟩
    rw [hα1] at this
    exact this.symm

  apply hyz
  obtain ⟨l, hlK, hl⟩ := hinner
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  set x₁ := l⁻¹ * x * l with hx₁
  have hx₁K : x₁ ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hlK) hx) hlK
  have e0 : S.z⁻¹ * x * S.z = x₁ := hl x hx
  have e1 : S.z⁻¹ * x = x₁ * S.z⁻¹ := by rw [← e0]; group
  have e2 : y⁻¹ * x₁ = x₁ * y⁻¹ := by
    have := hyc x₁ hx₁K
    calc y⁻¹ * x₁ = y⁻¹ * (y * x₁ * y⁻¹) := by rw [this]
      _ = x₁ * y⁻¹ := by group
  have e3 : S.z * x₁ = x * S.z := by rw [← e0]; group
  have e4 : y * x = x * y := by
    have := hyc x hx
    calc y * x = y * x * y⁻¹ * y := by group
      _ = x * y := by rw [this]
  calc x * (y * S.z * y⁻¹ * S.z⁻¹) = (x * y) * S.z * y⁻¹ * S.z⁻¹ := by group
    _ = (y * x) * S.z * y⁻¹ * S.z⁻¹ := by rw [e4]
    _ = y * (x * S.z) * y⁻¹ * S.z⁻¹ := by group
    _ = y * (S.z * x₁) * y⁻¹ * S.z⁻¹ := by rw [e3]
    _ = y * S.z * (x₁ * y⁻¹) * S.z⁻¹ := by group
    _ = y * S.z * (y⁻¹ * x₁) * S.z⁻¹ := by rw [e2]
    _ = y * S.z * y⁻¹ * (x₁ * S.z⁻¹) := by group
    _ = y * S.z * y⁻¹ * (S.z⁻¹ * x) := by rw [e1]
    _ = y * S.z * y⁻¹ * S.z⁻¹ * x := by group

end CFSG.Quasithin.H13.A5
