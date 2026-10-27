module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroKFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb
import CFSG.Quasithin.Background.A1cA133

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem card_centerOf_of_nonabelian {p : ℕ} [hp : Fact p.Prime] {X : Subgroup G}
    (hX : Nat.card X = p ^ 3) (hnab : ∃ a ∈ X, ∃ b ∈ X, a * b ≠ b * a) :
    Nat.card (centerOf X) = p := by
  rw [A1c.centerOf_eq_map_center, Subgroup.card_map_of_injective X.subtype_injective]
  have hXp : IsPGroup p ↥X := IsPGroup.of_card hX
  have : Nontrivial ↥X := by
    rw [← Finite.one_lt_card_iff_nontrivial, hX]
    exact Nat.one_lt_pow (by norm_num) hp.out.one_lt
  have hZnt : Nontrivial (Subgroup.center ↥X) := hXp.center_nontrivial
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow hp.out).mp
    (hX ▸ Subgroup.card_subgroup_dvd_card (Subgroup.center ↥X))
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  have hcomm : ¬ ∀ x y : ↥X, x * y = y * x := fun h =>
    hab (congrArg Subtype.val (h ⟨a, ha⟩ ⟨b, hb⟩))
  interval_cases k
  · exfalso
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr hZnt).ne' hk
  · simpa using hk
  · exfalso
    have hq : Nat.card (↥X ⧸ Subgroup.center ↥X) = p := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥X)
      rw [hX, hk] at h
      have hp0 : 0 < p ^ 2 := pow_pos hp.out.pos 2
      have : p ^ 3 = p * p ^ 2 := by ring
      rw [this] at h
      exact (Nat.eq_of_mul_eq_mul_right hp0 h).symm
    have : IsCyclic (↥X ⧸ Subgroup.center ↥X) := isCyclic_of_prime_card hq
    have hc := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center ↥X)) (by rw [QuotientGroup.ker_mk'])
    exact hcomm fun x y => hc.is_comm.comm x y
  · exfalso
    have htop : Subgroup.center ↥X = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hk, ← hX])
    exact hcomm fun x y => (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top y) x)

structure D1IbCubeThreeData (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (z : G) : Prop where
  data : D1OneSmallData p P M H R Rbar K
  elt : D1SmallCZElt p H R K z
  dec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i
  exp : ∀ r ∈ R, r ^ p = 1
  card_T : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
    Subgroup (H ⧸ primeComplementCore (G := H) p)) = p ^ 3

namespace D1IbCubeThreeData

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem prime (hc : D1IbCubeThreeData p P M H R Rbar K z) : p.Prime := hc.data.cfg.red.prime

theorem le_centralizer (hc : D1IbCubeThreeData p P M H R Rbar K z) :
    R ≤ Subgroup.centralizer ({z} : Set G) :=
  hc.data.le_centralizer_czElt hc.elt

theorem card_d1LiftX (hc : D1IbCubeThreeData p P M H R Rbar K z) :
    Nat.card (d1LiftX p H R K) = p ^ 3 ∧ z ∉ d1LiftX p H R K := by
  obtain ⟨hzT, hT⟩ := hc.data.d1LiftX_facts hc.elt
  exact ⟨hT.trans hc.card_T, hzT⟩

theorem nonabelian (hc : D1IbCubeThreeData p P M H R Rbar K z) (hShape : KFactSmallSylowShape) :
    ∃ a ∈ d1LiftX p H R K, ∃ b ∈ d1LiftX p H R K, a * b ≠ b * a := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T₁, hT₁, hs, hnab, hcat, hT₁nc, hΓ, -⟩ := hc.data.exists_sylow
  have hT₁card : Nat.card T₁ = p ^ 3 := by
    rw [← hc.card_T, ← hT₁, Subgroup.card_map_of_injective K.subtype_injective]
  rcases hShape K hs hnab hcat p hp hc.data.cfg.red.ne_two T₁ hT₁nc hΓ hc.data.small with
    h | ⟨-, hZ⟩
  · exfalso
    rw [hT₁card] at h
    exact absurd (Nat.pow_right_injective hp.two_le h) (by norm_num)
  have hnc : ∃ a b : (T₁ : Subgroup K), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have htop : Subgroup.center (T₁ : Subgroup K) = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => hcon y x
    rw [htop, Subgroup.card_top, hT₁card] at hZ
    have := Nat.pow_right_injective hp.two_le (hZ.trans (pow_one p).symm)
    omega
  obtain ⟨a, b, hab⟩ := hnc
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  have hlift : ∀ c : (T₁ : Subgroup K), ∃ t : H, t ∈ R.subgroupOf H ∧ π t ∈ K ∧
      π t = ((c : K) : H ⧸ primeComplementCore (G := H) p) := by
    intro c
    have hc' : ((c : K) : H ⧸ primeComplementCore (G := H) p) ∈
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K := by
      rw [← hT₁]
      exact ⟨c, c.2, rfl⟩
    obtain ⟨hcR, hcK⟩ := hc'
    rw [hc.data.cfg.rbar] at hcR
    obtain ⟨t, ht, hteq⟩ := hcR
    exact ⟨t, ht, hteq ▸ hcK, hteq⟩
  obtain ⟨s, hsR, hsK, hseq⟩ := hlift a
  obtain ⟨t, htR, htK, hteq⟩ := hlift b
  refine ⟨s, ⟨s, ⟨hsR, hsK⟩, rfl⟩, t, ⟨t, ⟨htR, htK⟩, rfl⟩, fun hst => hab ?_⟩
  have h1 : π (s * t) = π (t * s) := by
    congr 1
    exact Subtype.ext hst
  rw [map_mul, map_mul, hseq, hteq] at h1
  exact Subtype.ext (Subtype.ext h1)

theorem card_Z (hc : D1IbCubeThreeData p P M H R Rbar K z) (hShape : KFactSmallSylowShape) :
    Nat.card (centerOf (d1LiftX p H R K)) = p := by
  have : Fact p.Prime := ⟨hc.prime⟩
  exact card_centerOf_of_nonabelian hc.card_d1LiftX.1 (hc.nonabelian hShape)

theorem commute_z (hc : D1IbCubeThreeData p P M H R Rbar K z) {r : G} (hr : r ∈ R) :
    r * z = z * r :=
  Subgroup.mem_centralizer_singleton_iff.mp (hc.le_centralizer hr)

theorem centerOf_le_centralizer (hc : D1IbCubeThreeData p P M H R Rbar K z) {c : G}
    (hcZ : c ∈ centerOf (d1LiftX p H R K)) {r : G} (hr : r ∈ R) : c * r = r * c := by
  obtain ⟨t, ht, i, rfl⟩ := hc.dec r hr
  have hct : c * t = t * c := (Subgroup.mem_centralizer_iff.mp hcZ.2 t ht).symm
  have hcz : c * z ^ i = z ^ i * c :=
    ((Commute.pow_right (hc.commute_z (d1LiftX_le p H R K hcZ.1)) i).symm.eq).symm
  calc c * (t * z ^ i) = (c * t) * z ^ i := by group
    _ = t * (c * z ^ i) := by rw [hct]; group
    _ = t * z ^ i * c := by rw [hcz]; group

theorem mem_centerOf_of_comm (_hc : D1IbCubeThreeData p P M H R Rbar K z) {c : G}
    (hcT : c ∈ d1LiftX p H R K) (hcR : ∀ r ∈ R, c * r = r * c) :
    c ∈ centerOf (d1LiftX p H R K) :=
  ⟨hcT, Subgroup.mem_centralizer_iff.mpr fun t ht =>
    (hcR t (d1LiftX_le p H R K ht)).symm⟩

theorem elem_sup_zpowers (hc : D1IbCubeThreeData p P M H R Rbar K z) (hShape : KFactSmallSylowShape)
    {t : G} (ht : t ∈ d1LiftX p H R K) (htZ : t ∉ centerOf (d1LiftX p H R K)) :
    centerOf (d1LiftX p H R K) ⊔ Subgroup.zpowers t ≤ d1LiftX p H R K ∧
      IsElemAbelian p (centerOf (d1LiftX p H R K) ⊔ Subgroup.zpowers t) ∧
      Nat.card (centerOf (d1LiftX p H R K) ⊔ Subgroup.zpowers t : Subgroup G) = p ^ 2 := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  set T := d1LiftX p H R K with hTdef
  set Z₀ := centerOf T
  set X := Z₀ ⊔ Subgroup.zpowers t
  obtain ⟨hTcard, -⟩ := hc.card_d1LiftX
  have hTR : T ≤ R := d1LiftX_le p H R K
  have hXT : X ≤ T := sup_le inf_le_left (Subgroup.zpowers_le.mpr ht)
  have ht1 : t ≠ 1 := fun h => htZ (h ▸ Z₀.one_mem)
  have htp : orderOf t = p := by
    have h1 : t ^ p = 1 := hc.exp t (hTR ht)
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one h1) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ht1
    · exact h
  have hinf : Z₀ ⊓ Subgroup.zpowers t = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
    by_contra hy1
    exact htZ ((Subgroup.zpowers_le.mpr hy.1)
      (mem_zpowers_of_mem_zpowers_of_prime hp htp hy.2 hy1))
  have hcomm : X ≤ Subgroup.centralizer (X : Set G) := by
    have hZC : Z₀ ≤ Subgroup.centralizer (X : Set G) := fun c hcZ =>
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (Subgroup.mem_centralizer_iff.mp hcZ.2 y (hXT hy))
    refine sup_le hZC (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr ?_))
    intro y hy
    have hX' : X ≤ Subgroup.centralizer ({t} : Set G) := by
      refine sup_le (fun c hcZ => ?_) ?_
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hcZ.2 t ht).symm
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hX' hy))
  have hXne : X ≠ T := by
    intro hXeq
    obtain ⟨a, ha, a', ha', haa⟩ := hc.nonabelian hShape
    rw [← hTdef, ← hXeq] at ha ha'
    exact haa (Subgroup.mem_centralizer_iff.mp (hcomm ha') a ha)
  refine ⟨hXT, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hc.exp x (hTR (hXT hx))⟩, ?_⟩
  · exact (Subgroup.mem_centralizer_iff.mp (hcomm b.2) a a.2)
  · have h1 := mul_card_le_of_inf_eq_bot (le_sup_left : Z₀ ≤ X) le_sup_right hinf
    rw [hc.card_Z hShape, Nat.card_zpowers, htp] at h1
    obtain ⟨m, hm3, hm⟩ := (Nat.dvd_prime_pow hp).mp (hTcard ▸ Subgroup.card_dvd_of_le hXT)
    rw [hm] at h1 ⊢
    have hm2 : 2 ≤ m := by
      by_contra hlt
      have : p ^ m ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      nlinarith [hp.two_le]
    interval_cases m
    · rfl
    · exact absurd (Subgroup.eq_of_le_of_card_ge hXT (by rw [hm, hTcard])) hXne

theorem centerOf_le_commutator_self (hc : D1IbCubeThreeData p P M H R Rbar K z)
    (hShape : KFactSmallSylowShape) :
    centerOf (d1LiftX p H R K) ≤ ⁅d1LiftX p H R K, d1LiftX p H R K⁆ := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  set T := d1LiftX p H R K
  have hTp : IsPGroup p ↥T := IsPGroup.of_card hc.card_d1LiftX.1
  have : Group.IsNilpotent ↥T := hTp.isNilpotent
  set N : Subgroup ↥T := ⁅(⊤ : Subgroup ↥T), ⊤⁆
  have hN : N ≠ ⊥ := by
    intro hbot
    obtain ⟨a, ha, b, hb, hab⟩ := hc.nonabelian hShape
    have h1 : _ ∈ N := Subgroup.commutator_mem_commutator (G := ↥T)
      (Subgroup.mem_top (⟨a, ha⟩ : ↥T)) (Subgroup.mem_top (⟨b, hb⟩ : ↥T))
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact hab (congrArg Subtype.val h1)
  have hNZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hN
  have hZcard : Nat.card (Subgroup.center ↥T) = p := by
    rw [← hc.card_Z hShape, A1c.centerOf_eq_map_center,
      Subgroup.card_map_of_injective T.subtype_injective]
  have hZle : Subgroup.center ↥T ≤ N := by
    have h1 : Nat.card (N ⊓ Subgroup.center ↥T : Subgroup ↥T) ∣ p := by
      rw [← hZcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hNZ
    · have := Subgroup.eq_of_le_of_card_ge (inf_le_right : N ⊓ Subgroup.center ↥T ≤ _)
        (by rw [hZcard, h])
      exact this ▸ inf_le_left
  rw [A1c.centerOf_eq_map_center]
  calc (Subgroup.center ↥T).map T.subtype ≤ N.map T.subtype := Subgroup.map_mono hZle
    _ = ⁅T, T⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end D1IbCubeThreeData

end CFSG.AGLEmbedding
