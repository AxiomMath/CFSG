module

public import CFSG.LargeExtraspecial.S14Nine
public import CFSG.LargeExtraspecial.S14Six

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.LargeExtraspecial.S4
open scoped commutatorElement

theorem le_of_forall_mul_of_perfect {X : Type*} [Group X] {R K N : Subgroup X} [Finite R]
    (hK : ∀ r ∈ R, ∀ k ∈ K, r * k * r⁻¹ ∈ K) (hNR : N ≤ R) (hN : IsPGroup 2 N)
    (hRKN : ∀ r ∈ R, ∃ k ∈ K, ∃ n ∈ N, r = k * n) (hperf : ⁅R, R⁆ = R) : R ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K' := K.subgroupOf R with hK'
  have hK'n : K'.Normal := ⟨fun a ha r => by
    rw [hK', mem_subgroupOf] at ha ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hK r r.2 a ha⟩
  set π := QuotientGroup.mk' K' with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective K'
  have h2 : IsPGroup 2 (R ⧸ K') := by
    intro q
    obtain ⟨r, rfl⟩ := hπ q
    obtain ⟨k, hk, n, hn, hr⟩ := hRKN r r.2
    obtain ⟨j, hj⟩ := hN ⟨n, hn⟩
    refine ⟨j, ?_⟩
    have hkR : k ∈ R := by
      have e : k = (r : X) * n⁻¹ := by rw [hr]; group
      rw [e]
      exact mul_mem r.2 (inv_mem (hNR hn))
    have e : r = ⟨k, hkR⟩ * ⟨n, hNR hn⟩ := Subtype.ext hr
    have hk1 : π ⟨k, hkR⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hk)
    have hn1 : (⟨n, hNR hn⟩ : R) ^ 2 ^ j = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hj
      simpa using this
    rw [e, map_mul, hk1, one_mul, ← map_pow, hn1, map_one]
  have hR' : ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆ = (⊤ : Subgroup R) := by
    apply map_injective R.subtype_injective
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype, hperf]
  have hperfQ : ⁅(⊤ : Subgroup (R ⧸ K')), (⊤ : Subgroup (R ⧸ K'))⁆ = ⊤ := by
    have h1 := map_commutator (⊤ : Subgroup R) ⊤ π
    rw [hR', map_top_of_surjective π hπ] at h1
    exact h1.symm
  by_contra hle
  have hne : (⊤ : Subgroup (R ⧸ K')) ≠ ⊥ := by
    intro h
    apply hle
    intro r hr
    have h1 : π ⟨r, hr⟩ = 1 := by
      have := mem_top (π ⟨r, hr⟩)
      rwa [h, mem_bot] at this
    exact mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  exact commutator_ne_of_isPGroup h2 hne hperfQ

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem le_Nbar_or_le_of_normal (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    (hs : IsSimpleGroup (RmodN S g t)) (hperf : ⁅Rbar S g t, Rbar S g t⁆ = Rbar S g t)
    (hN2 : IsPGroup 2 (Nbar S g t)) {K : Subgroup S.O} (hKR : K ≤ Rbar S g t)
    (hK : ∀ r ∈ Rbar S g t, ∀ k ∈ K, r * k * r⁻¹ ∈ K) :
    K ≤ Nbar S g t ∨ Rbar S g t ≤ K := by
  obtain ⟨f, hf⟩ : ∃ f, f = resV haQ t := ⟨_, rfl⟩
  have hrange : f.range = RmodN S g t := by rw [hf]; exact range_resV haQ t
  have hker : ∀ x, f x = 1 ↔ (x : S.O) ∈ Nbar S g t := fun x => by
    rw [hf]; exact resV_eq_one_iff haQ x
  have hs' : IsSimpleGroup f.range :=
    (MulEquiv.isSimpleGroup_congr (MulEquiv.subgroupCongr hrange)).mpr hs
  set K' := K.subgroupOf (Rbar S g t) with hK'
  have hK'n : K'.Normal := ⟨fun a ha r => by
    rw [hK', mem_subgroupOf] at ha ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hK r r.2 a ha⟩
  have hIn : (K'.map f.rangeRestrict).Normal := hK'n.map _ f.rangeRestrict_surjective
  rcases hs'.eq_bot_or_eq_top_of_normal (K'.map f.rangeRestrict) with h | h
  · left
    intro k hk
    have hmem : f.rangeRestrict ⟨k, hKR hk⟩ ∈ K'.map f.rangeRestrict :=
      mem_map_of_mem _ (mem_subgroupOf.mpr hk)
    have h1 := (Subgroup.eq_bot_iff_forall _).mp h _ hmem
    exact (hker _).mp (congrArg Subtype.val h1)
  · right
    refine le_of_forall_mul_of_perfect hK (fun _ hx => Nbar_le_Rbar hx) hN2 (fun r hr => ?_) hperf
    have hmem : f.rangeRestrict ⟨r, hr⟩ ∈ K'.map f.rangeRestrict :=
      (Subgroup.eq_top_iff' _).mp h _
    obtain ⟨k, hk, hkr⟩ := mem_map.mp hmem
    have hkr' : f k = f ⟨r, hr⟩ := congrArg Subtype.val hkr
    refine ⟨k, mem_subgroupOf.mp hk, ((k⁻¹ * ⟨r, hr⟩ : Rbar S g t) : S.O), ?_, ?_⟩
    · refine (hker _).mp ?_
      rw [map_mul, map_inv, hkr', inv_mul_cancel]
    · simp

theorem conj_mem_Mbar0 {x y : S.O} (hx : x ∈ S.Mbar) (hy : y ∈ (Mbar0 S).map S.Mbar.subtype) :
    x * y * x⁻¹ ∈ (Mbar0 S).map S.Mbar.subtype := by
  obtain ⟨y, hy, rfl⟩ := hy
  exact ⟨⟨x, hx⟩ * y * (⟨x, hx⟩ : S.Mbar)⁻¹, (timmesfeldFStar_normal S.Mbar).conj_mem y hy _, rfl⟩

theorem conj_Rbar_of_mem_Ct {t c r : S.O} (hc : c ∈ Ct S t) (hr : r ∈ Rbar S g t) :
    c * r * c⁻¹ ∈ Rbar S g t := by
  obtain ⟨k, hk⟩ : ∃ k : S.M, S.ρ k = c := hc.1
  have hkt : S.ρ k * t = t * S.ρ k := by
    rw [hk]
    exact mem_centralizer_singleton_iff.mp hc.2
  have := conj_mem_Rbar hkt hr
  rwa [hk] at this

theorem comm_mem_zpowers_of_extraspecial {X : Type*} [Group X] {N : Subgroup X}
    (hN : IsExtraspecialPGroup 2 N) {t : X} (htN : t ∈ N) (ht1 : t ≠ 1)
    (htc : ∀ y ∈ N, y * t = t * y) {x y : X} (hx : x ∈ N) (hy : y ∈ N) :
    x * y * x⁻¹ * y⁻¹ ∈ zpowers t := by
  have htc' : (⟨t, htN⟩ : N) ∈ center N := by
    rw [mem_center_iff]
    intro v
    exact Subtype.ext (htc v v.2)
  have hc := CFSG.RankThree.Literature.FSmith.commutatorElement_mem_center hN ⟨x, hx⟩ ⟨y, hy⟩
  by_cases h1 : ⁅(⟨x, hx⟩ : N), (⟨y, hy⟩ : N)⁆ = 1
  · have e := congrArg Subtype.val h1
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
      OneMemClass.coe_one] at e
    rw [e]
    exact one_mem _
  · have h2 := CFSG.RankThree.Literature.FSmith.eq_of_mem_center hN hc htc' h1
      (fun e => ht1 (congrArg Subtype.val e))
    have e := congrArg Subtype.val h2
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at e
    rw [e]
    exact mem_zpowers t

theorem sq_mem_zpowers_of_extraspecial {X : Type*} [Group X] {N : Subgroup X} [Finite N]
    (hN : IsExtraspecialPGroup 2 N) {t : X} (htN : t ∈ N) (ht1 : t ≠ 1)
    (htc : ∀ y ∈ N, y * t = t * y) {x : X} (hx : x ∈ N) : x * x ∈ zpowers t := by
  have htc' : (⟨t, htN⟩ : N) ∈ center N := by
    rw [mem_center_iff]
    intro v
    exact Subtype.ext (htc v v.2)
  have hc := CFSG.RankThree.Literature.FSmith.sq_mem_center hN ⟨x, hx⟩
  by_cases h1 : (⟨x, hx⟩ : N) ^ 2 = 1
  · have e := congrArg Subtype.val h1
    simp only [pow_two, Subgroup.coe_mul, OneMemClass.coe_one] at e
    rw [e]
    exact one_mem _
  · have h2 := CFSG.RankThree.Literature.FSmith.eq_of_mem_center hN hc htc' h1
      (fun e => ht1 (congrArg Subtype.val e))
    have e := congrArg Subtype.val h2
    simp only [pow_two, Subgroup.coe_mul] at e
    rw [e]
    exact mem_zpowers t

theorem odd_card_Mbar0 {t : S.O} (htM : t ∈ S.Mbar) (htt : t * t = 1)
    (hC : ∀ c ∈ (Mbar0 S).map S.Mbar.subtype, c * t = t * c → c = 1) :
    Odd (Nat.card (Mbar0 S)) := by
  have : (Mbar0 S).Normal := timmesfeldFStar_normal S.Mbar
  set φ : MulAut (Mbar0 S) := MulAut.conjNormal (⟨t, htM⟩ : S.Mbar) with hφ
  have hφv : ∀ m : Mbar0 S, ((φ m : S.Mbar) : S.O) = t * ((m : S.Mbar) : S.O) * t⁻¹ :=
    fun m => by rw [hφ, MulAut.conjNormal_apply]; rfl
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  refine MonoidHom.FixedPointFree.odd_card_of_involutive (φ := φ) (fun m hm => ?_) (fun m => ?_)
  · have hm' := congrArg (fun x : Mbar0 S => ((x : S.Mbar) : S.O)) hm
    simp only [hφv] at hm'
    have hc : ((m : S.Mbar) : S.O) * t = t * ((m : S.Mbar) : S.O) := by
      calc ((m : S.Mbar) : S.O) * t = t * ((m : S.Mbar) : S.O) * t⁻¹ * t := by rw [hm']
        _ = t * ((m : S.Mbar) : S.O) := by group
    have h1 := hC _ ⟨m, m.2, rfl⟩ hc
    exact Subtype.ext (Subtype.ext h1)
  · apply Subtype.ext
    apply Subtype.ext
    rw [hφv, hφv, htinv]
    calc t * (t * ((m : S.Mbar) : S.O) * t) * t = (t * t) * ((m : S.Mbar) : S.O) * (t * t) := by
          group
      _ = ((m : S.Mbar) : S.O) := by rw [htt, one_mul, mul_one]

theorem mem_Mbar0_of_le_Nbar {t : S.O} (hSt : Stage S g t)
    (hRp : ⁅Rbar S g t, Rbar S g t⁆ = Rbar S g t) (hext : IsExtraspecialPGroup 2 (Nbar S g t))
    (hsim : IsSimpleGroup (Mbar0 S)) (h7 : Concl14_7 S g t)
    (hK : Rbar S g t ⊓ (Mbar0 S).map S.Mbar.subtype ≤ Nbar S g t) :
    t ∈ (Mbar0 S).map S.Mbar.subtype := by
  have haQ := hSt.hyp4.conj_mem
  have htN : t ∈ Nbar S g t := S6.self_mem_Nbar hSt.hyp4 hSt.mem
  have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g hSt.mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ hSt.mem
  have htc : ∀ y ∈ Nbar S g t, y * t = t * y := fun y hy =>
    commute_of_mem_Rbar haQ (Nbar_le_Rbar hy)
  set M0 := (Mbar0 S).map S.Mbar.subtype with hM0
  by_cases hex : ∃ k ∈ Rbar S g t ⊓ M0, k ≠ 1
  ·
    obtain ⟨k, hk, hk1⟩ := hex
    obtain ⟨hkR, hkM⟩ := Subgroup.mem_inf.mp hk
    have hkN := hK hk
    by_cases hkc : ∀ n ∈ Nbar S g t, n * k = k * n
    · have htc' : (⟨t, htN⟩ : Nbar S g t) ∈ center (Nbar S g t) := by
        rw [mem_center_iff]
        intro v
        exact Subtype.ext (htc v v.2)
      have hkc' : (⟨k, hkN⟩ : Nbar S g t) ∈ center (Nbar S g t) := by
        rw [mem_center_iff]
        intro v
        exact Subtype.ext (hkc v v.2)
      have e := CFSG.RankThree.Literature.FSmith.eq_of_mem_center hext hkc' htc'
        (fun h => hk1 (congrArg Subtype.val h)) (fun h => hSt.ne_one (congrArg Subtype.val h))
      have e' : k = t := congrArg Subtype.val e
      rw [← e']
      exact hkM
    · push Not at hkc
      obtain ⟨n, hn, hnk⟩ := hkc
      have hc := comm_mem_zpowers_of_extraspecial hext htN hSt.ne_one htc hn hkN
      rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp hc with h | h
      · exact absurd (by calc n * k = (n * k * n⁻¹ * k⁻¹) * k * n := by group
          _ = k * n := by rw [h, one_mul]) hnk
      · rw [← h]
        have hnM : n ∈ S.Mbar := Rbar_le_Mbar (Nbar_le_Rbar hn)
        exact mul_mem (conj_mem_Mbar0 hnM hkM) (inv_mem hkM)
  ·
    push Not at hex
    exfalso
    have hC : ∀ c ∈ M0, c * t = t * c → c = 1 := by
      intro c hcM hct
      have hcMb : c ∈ S.Mbar := map_subtype_le _ hcM
      have hcCt : c ∈ Ct S t := ⟨hcMb, mem_centralizer_singleton_iff.mpr hct⟩
      have hcomm : ∀ r ∈ Rbar S g t, c * r * c⁻¹ * r⁻¹ = 1 := fun r hr => by
        refine hex _ (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
        · exact mul_mem (conj_Rbar_of_mem_Ct hcCt hr) (inv_mem hr)
        · have e : c * r * c⁻¹ * r⁻¹ = c * (r * c⁻¹ * r⁻¹) := by group
          rw [e]
          exact mul_mem hcM (conj_mem_Mbar0 (Rbar_le_Mbar hr) (inv_mem hcM))
      have hcN : c ∈ Nbar S g t := h7.1 c hcMb fun y hy => by
        rw [hcomm y (Nbar_le_Rbar hy)]
        exact one_mem _
      exact hex c (Subgroup.mem_inf.mpr ⟨Nbar_le_Rbar hcN, hcM⟩)
    have hodd := odd_card_Mbar0 htM htt hC
    have hO := oddCore_Mbar_eq_bot hSt hRp
    have hle := S5.le_timmesfeldOddCore (timmesfeldFStar_normal S.Mbar) hodd
    rw [hO, le_bot_iff] at hle
    have := hsim.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this hle

end CFSG.LargeExtraspecial.S14
