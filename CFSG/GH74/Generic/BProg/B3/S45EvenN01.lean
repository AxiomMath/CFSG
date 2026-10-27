module

public import CFSG.GH74.Generic.BProg.B3.S45EvenDefs
public import CFSG.GH74.Generic.BProg.B3.RankC
public import CFSG.GH74.Generic.BProg.B3.Lemma212S45

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.Generic
  CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LocalCores Subgroup
open CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic.BProg.B3.FalseCtxS45

namespace S45EvenN01

section Small

theorem eq_one_of_proj {G : Type} [Group G] [Finite G] (x : G) {u : ↥(centralizer ({x} : Set G))}
    {k : ℕ} (hu : u ^ (2 ^ k) = 1) (h : proj x u = 1) : u = 1 := by
  have hord : orderOf u = 1 :=
    Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_left.mpr (proj_odd x u h)).pow_left k).symm
      (orderOf_dvd_of_pow_eq_one hu)
  exact orderOf_eq_one_iff.mp hord

theorem sq_eq_one_of_two_elem {L : Type} [Group L] [Finite L] (hs : B2.FixFourS45.HasE8Sylow L)
    {l : L} {k : ℕ} (hl : l ^ (2 ^ k) = 1) : l ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (isPGroup_zpowers_of_pow_two_pow_eq_one hl).exists_le_sylow
  obtain ⟨hQel, -⟩ := hs.all Q
  have hlQ : l ∈ (Q : Subgroup L) := hQ (Subgroup.mem_zpowers l)
  have h2 : (⟨l, hlQ⟩ : ↥(Q : Subgroup L)) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hQel.exponent_dvd_p _
  exact congrArg Subtype.val h2

theorem sq_eq_one_of_mem {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hs : B2.FixFourS45.HasE8Sylow ↥L) {l : X} (hl : l ∈ L) {k : ℕ} (hlk : l ^ (2 ^ k) = 1) :
    l ^ 2 = 1 := by
  have h := sq_eq_one_of_two_elem hs (l := (⟨l, hl⟩ : ↥L)) (k := k) (Subtype.ext (by simpa using hlk))
  exact congrArg Subtype.val h

end Small

section Shapes


theorem e8_of_shapes {L : Type} [Group L] [Finite L] (hq : IsQuasisimple L)
    (h : QShape4 L ∨ QShape5 L) : RankC.E8Data L ∧ B2.FixFourS45.HasE8Sylow L := by
  rcases h with h4 | h5
  · exact ⟨RankC.e8Data_of_qShape4 h4, (B2.FixFourS45.shape4_data h4).1⟩
  · exact ⟨RankC.e8Data_of_qShape5 hq h5, (B2.FixFourS45.shape5_data h5).1⟩

end Shapes

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_two_element {x a : G} (hx : orderOf x = 2) (hxY : x ∈ centralizer ({a} : Set G)) :
    ∀ {s : barQ ↥(centralizer ({a} : Set G))} {k : ℕ}, s ^ (2 ^ k) = 1 →
      tbar a x hxY * s = s * tbar a x hxY →
      ∃ p : ↥(centralizer ({a} : Set G)), (p : G) ∈ centralizer ({x} : Set G) ∧
        (∃ n : ℕ, (p : G) ^ (2 ^ n) = 1) ∧ barMk ↥(centralizer ({a} : Set G)) p = s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := centralizer ({a} : Set G) with hY
  intro s k hsk hcomm
  set R : Subgroup ↥Y := pPrimeCore 2 ↥Y with hR
  have hRodd : Odd (Nat.card R) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  set M₀ : Subgroup G := centralizer ({x} : Set G) ⊓ Y with hM₀
  have hM₀Y : M₀ ≤ Y := inf_le_right
  have hM₀x : M₀ ≤ centralizer ({x} : Set G) := inf_le_left
  set f : ↥M₀ →* barQ ↥Y := (barMk ↥Y).comp (Subgroup.inclusion hM₀Y) with hf
  set T' : Subgroup (barQ ↥Y) := zpowers s with hT'
  have hT'p : IsPGroup 2 ↥T' := isPGroup_zpowers_of_pow_two_pow_eq_one hsk
  have hordY : orderOf (⟨x, hxY⟩ : ↥Y) = 2 := by rw [Subgroup.orderOf_mk]; exact hx
  have hT'f : T' ≤ f.range := by
    intro τ hτ
    have hcomm0 : tbar a x hxY * τ = τ * tbar a x hxY := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hτ
      exact (Commute.zpow_right (show Commute (tbar a x hxY) s from hcomm) n).eq
    have hcomm' : ∀ a' ∈ zpowers (⟨x, hxY⟩ : ↥Y),
        QuotientGroup.mk' R a' * τ = τ * QuotientGroup.mk' R a' := by
      intro a' ha'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha'
      rw [map_zpow]
      exact (Commute.zpow_left (show Commute (tbar a x hxY) τ from hcomm0) k).eq
    obtain ⟨g, hgψ, hgc⟩ := B1.centralizer_quotient_of_pGroup R hRodd
      (B1.isPGroup_two_zpowers_of_orderOf hordY) hcomm'
    have hge : (⟨x, hxY⟩ : ↥Y) * g = g * ⟨x, hxY⟩ := hgc _ (mem_zpowers _)
    have hgM : (g : G) ∈ M₀ := ⟨Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val hge).symm, g.2⟩
    exact ⟨⟨g, hgM⟩, hgψ⟩
  obtain ⟨P, hPp, hPmap⟩ := exists_pGroup_lift f T' hT'p hT'f
  have hsT : s ∈ T' := Subgroup.mem_zpowers s
  rw [← hPmap] at hsT
  obtain ⟨p, hp, hps⟩ := hsT
  refine ⟨⟨(p : G), hM₀Y p.2⟩, hM₀x p.2, ?_, hps⟩
  obtain ⟨n, hn⟩ := hPp ⟨p, hp⟩
  exact ⟨n, by simpa using congrArg (fun z : ↥P => ((z : ↥M₀) : G)) hn⟩

end Lift

end S45EvenN01

section Consumer

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}


theorem N0_pow_eq_x (hc : Ctx21 G x K A a D J)
    (hP : QShape4 (↥K ⧸ pPrimeCore 2 ↥K) ∨ QShape5 (↥K ⧸ pPrimeCore 2 ↥K))
    {t : G} (ht : t ∈ centralizer ({x} : Set G)) {k : ℕ} (htk : t ^ (2 ^ k) = 1) (ht2 : t ^ 2 ≠ 1) :
    ∃ j : ℕ, 1 ≤ j ∧ t ^ (2 ^ j) = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx : orderOf x = 2 := hc.circ.1.1.1.1
  have hILo : IsILo 2 x K := hc.circ.1.1.1
  have hKpc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hILo.2.2
  have hgen : Gen4 (CentralizerBar x) := gen4_centralizerBar hc.hyp.gen4 x
  have hLc : IsComponent (imgBar x K) := C3.Layer1.PumpCalc.isComponent_bar hKpc
  obtain ⟨eMK⟩ := C3.Layer1.PumpCalc.kBar_equiv_bar hKpc
  have eMK' : (↥K ⧸ pPrimeCore 2 ↥K) ≃* ↥(imgBar x K) := eMK
  obtain ⟨hd, hs⟩ := S45EvenN01.e8_of_shapes hLc.1 (qshape_transport eMK' hP)
  have hN : (imgBar x K).Normal := RankC.normal_of_gen4 hgen hLc hd
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  let tc : ↥(centralizer ({x} : Set G)) := ⟨t, ht⟩
  have htc : tc ^ (2 ^ k) = 1 := Subtype.ext (by simpa [tc] using htk)
  have htc2 : tc ^ 2 ≠ 1 := fun h => ht2 (by simpa [tc] using congrArg Subtype.val h)
  have hrk : (proj x tc) ^ (2 ^ k) = 1 := by rw [← map_pow, htc, map_one]
  obtain ⟨l, hlL, y, hyC, hry⟩ := RankC.exists_mul_of_two_element hd hrk
  have hcomm : Commute l y := Subgroup.mem_centralizer_iff.mp hyC l hlL
  have hpow : l ^ (2 ^ k) * y ^ (2 ^ k) = 1 := by
    rw [← hcomm.mul_pow, ← hry]
    exact hrk
  have hlk : l ^ (2 ^ k) = 1 := by
    have hyk : y ^ (2 ^ k) ∈ centralizer ((imgBar x K : Subgroup _) : Set _) := pow_mem hyC _
    have heq : l ^ (2 ^ k) = (y ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_left hpow
    have h1 : (⟨l ^ (2 ^ k), pow_mem hlL _⟩ : ↥(imgBar x K)) = 1 := by
      refine hd.center _ (fun g => Subtype.ext ?_)
      show (g : CentralizerBar x) * l ^ (2 ^ k) = l ^ (2 ^ k) * (g : CentralizerBar x)
      rw [heq]
      exact Subgroup.mem_centralizer_iff.mp (inv_mem hyk) g g.2
    exact congrArg Subtype.val h1
  have hyk : y ^ (2 ^ k) = 1 := by
    rw [hlk, one_mul] at hpow
    exact hpow
  have hl2 : l ^ 2 = 1 := S45EvenN01.sq_eq_one_of_mem hs hlL hlk
  have hy2 : y ^ 2 ≠ 1 := by
    intro hy2
    have h1 : proj x (tc ^ 2) = 1 := by
      rw [map_pow, hry, hcomm.mul_pow, hl2, hy2, one_mul]
    have h2 : (tc ^ 2) ^ (2 ^ k) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, htc, one_pow]
    exact htc2 (S45EvenN01.eq_one_of_proj x h2 h1)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hyk)
  have hm2 : 2 ≤ m := by
    by_contra hlt
    apply hy2
    have h1 : orderOf y ∣ 2 := by
      rw [hm]
      exact (Nat.pow_dvd_pow 2 (by omega : m ≤ 1))
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hj1 : 1 ≤ j := by omega
  have hy0sq : y ^ (2 ^ j) * y ^ (2 ^ j) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', ← hm]
    exact pow_orderOf_eq_one y
  have hy0ne : y ^ (2 ^ j) ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by positivity) (by rw [hm]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hxbar2 : xbar x * xbar x = 1 := xbar_mul_self hx
  have hxbar1 : xbar x ≠ 1 := xbar_ne_one hx
  have hxbarC : ∀ z : CentralizerBar x, z * xbar x = xbar x * z := fun z =>
    Subgroup.mem_center_iff.mp (xbar_mem_center x) z
  have hy0x : xbar x = y ^ (2 ^ j) := by
    by_contra hne
    refine B1.false_of_central_involution_pair hgen (K := imgBar x K) (a := xbar x)
      (b := y ^ (2 ^ j)) hxbar2 hy0sq hxbar1 hy0ne hne hxbarC
      (fun k hk => (Subgroup.mem_centralizer_iff.mp (pow_mem hyC _) k hk).symm) (r := 2) hd.cert
      ?_ le_rfl ?_
    · intro z hz
      left
      have h1 := hd.center z (fun g => Subgroup.mem_center_iff.mp hz g)
      exact congrArg Subtype.val h1
    · intro haL
      exfalso
      apply hxbar1
      have h1 := hd.center ⟨xbar x, haL⟩ (fun g => Subtype.ext (hxbarC g))
      exact congrArg Subtype.val h1
  refine ⟨j, hj1, ?_⟩
  have hl2j : l ^ (2 ^ j) = 1 := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [pow_succ, mul_comm, pow_mul, hl2, one_pow]
  have hrj : proj x (tc ^ (2 ^ j)) = xbar x := by
    rw [map_pow, hry, hcomm.mul_pow, hl2j, one_mul]
    exact hy0x.symm
  have hproj : proj x (tc ^ (2 ^ j) * (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G)))⁻¹) = 1 := by
    rw [map_mul, map_inv, hrj]
    exact mul_inv_cancel _
  have hcx : Commute tc (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G))) :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp ht)
  have hu : (tc ^ (2 ^ j) * (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G)))⁻¹) ^ (2 ^ (k + 1)) = 1 := by
    rw [((hcx.pow_left (2 ^ j)).inv_right).mul_pow, inv_pow]
    have h1 : (tc ^ (2 ^ j)) ^ (2 ^ (k + 1)) = 1 := by
      have : (tc ^ (2 ^ j)) ^ (2 ^ (k + 1)) = (tc ^ (2 ^ k)) ^ (2 ^ j * 2) := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
      rw [this, htc, one_pow]
    have h2 : (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G))) ^ (2 ^ (k + 1)) = 1 := by
      apply Subtype.ext
      show x ^ (2 ^ (k + 1)) = 1
      have hx2 : x ^ 2 = 1 := by
        have := pow_orderOf_eq_one x
        rwa [hx] at this
      rw [pow_succ, mul_comm, pow_mul, hx2, one_pow]
    rw [h1, h2, inv_one, mul_one]
  have hu1 := S45EvenN01.eq_one_of_proj x hu hproj
  have h3 : tc ^ (2 ^ j) = ⟨x, hxC⟩ := mul_inv_eq_one.mp hu1
  simpa [tc] using congrArg Subtype.val h3

theorem N1_evenEA (hc : Ctx21 G x K A a D J)
    (hP : QShape4 (↥K ⧸ pPrimeCore 2 ↥K) ∨ QShape5 (↥K ⧸ pPrimeCore 2 ↥K)) (hax : a ≠ x)
    (hxY : x ∈ centralizer ({a} : Set G)) (hxJ : x ∈ normalizer (J : Set G)) :
    EvenEA ↥(PumpCalc.bar a J) (yAut hc.obs.comp.1 hxY hxJ) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J := hc.obs.comp
  have hx : orderOf x = 2 := hc.circ.1.1.1.1
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hx1 : x ≠ 1 := fun h => by simp [h] at hx
  obtain ⟨n, hcen, -⟩ := Lemma212S45.shape45_data hP
  obtain ⟨E, hEK, hAE, hxE, hEel, hE4⟩ := exists_E hc hcen
  have hxA : x ∈ A := hAE ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hnc : x ∉ centralizerSection J (pPrimeCoreOf 2 J) := fun hcs =>
    (hc.cA_eq x hxA hcs).elim hx1 (fun h => hax h.symm)
  by_cases hxb : tbar a x hxY ∈ PumpCalc.bar a J
  · right
    refine ⟨⟨tbar a x hxY, hxb⟩, ?_, ?_, ?_⟩
    · apply Subtype.ext
      show barMk ↥(centralizer ({a} : Set G)) ⟨x, hxY⟩ * barMk ↥(centralizer ({a} : Set G)) ⟨x, hxY⟩ = 1
      rw [← map_mul]
      have : (⟨x, hxY⟩ : ↥(centralizer ({a} : Set G))) * ⟨x, hxY⟩ = 1 := Subtype.ext hx2
      rw [this, map_one]
    · intro hcenter
      apply yAut_ne_one hJ hxY hxJ hnc
      ext g
      rw [coe_yAut, MulAut.one_apply]
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hcenter g)
      exact mul_inv_eq_iff_eq_mul.mpr h1.symm
    · intro g
      apply Subtype.ext
      rw [coe_yAut]
      rfl
  · left
    intro s hs k hsk
    by_contra hs2
    have hcomm : tbar a x hxY * (s : barQ ↥(centralizer ({a} : Set G))) =
        (s : barQ ↥(centralizer ({a} : Set G))) * tbar a x hxY := by
      have h1 := congrArg (fun σ : ↥(PumpCalc.bar a J) => (σ : barQ ↥(centralizer ({a} : Set G)))) hs
      simp only [coe_yAut] at h1
      calc tbar a x hxY * (s : barQ ↥(centralizer ({a} : Set G)))
          = (tbar a x hxY * s * (tbar a x hxY)⁻¹) * tbar a x hxY := by group
        _ = (s : barQ ↥(centralizer ({a} : Set G))) * tbar a x hxY := by rw [h1]
    have hsk' : (s : barQ ↥(centralizer ({a} : Set G))) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hsk
      simpa using this
    obtain ⟨p, hpx, ⟨m, hpm⟩, hps⟩ := S45EvenN01.exists_lift_two_element hx hxY hsk' hcomm
    have hp2 : (p : G) ^ 2 ≠ 1 := by
      intro h
      apply hs2
      apply Subtype.ext
      show (s : barQ ↥(centralizer ({a} : Set G))) ^ 2 = 1
      rw [← hps, ← map_pow]
      have : p ^ 2 = 1 := Subtype.ext (by simpa using h)
      rw [this, map_one]
    obtain ⟨j, hj1, hpj⟩ := N0_pow_eq_x hc hP hpx hpm hp2
    apply hxb
    have h1 : (s : barQ ↥(centralizer ({a} : Set G))) ^ (2 ^ j) = tbar a x hxY := by
      rw [← hps, ← map_pow]
      have : p ^ (2 ^ j) = ⟨x, hxY⟩ := Subtype.ext (by simpa using hpj)
      rw [this]
    have h2 : ((s ^ (2 ^ j) : ↥(PumpCalc.bar a J)) : barQ ↥(centralizer ({a} : Set G))) ∈
        PumpCalc.bar a J := (s ^ (2 ^ j)).2
    rw [Subgroup.coe_pow, h1] at h2
    exact h2

end Consumer

end CFSG.GH74.Generic.BProg.B3
