module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.LocalAnalysis.SeitzReduction.FoursGroupExceptionalBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.EvenSmallLie CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open scoped Pointwise

theorem hypothesisOneStar_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : HypothesisOneStar X) : HypothesisOneStar Y := by
  intro x' u' hx' hu' E' hE'x hE'odd hE'u hE'inn
  set Φ : MulAut X ≃* MulAut Y := MulAut.congr e with hΦdef
  have hΦconj : ∀ a : X, Φ (MulAut.conj a) = MulAut.conj (e a) := by
    intro a
    ext y
    simp [hΦdef, MulAut.conj_apply]
  have hmem : ∀ (K : Subgroup (MulAut Y)) (w : MulAut X),
      w ∈ K.map Φ.symm.toMonoidHom ↔ Φ w ∈ K := by
    intro K w
    rw [mem_map_equiv, MulEquiv.symm_symm]
  have hx : Φ (Φ.symm x') = x' := Φ.apply_symm_apply x'
  have hu : Φ (Φ.symm u') = u' := Φ.apply_symm_apply u'
  have hcomm : ∀ c : X, MulAut.conj c * Φ.symm x' = Φ.symm x' * MulAut.conj c →
      MulAut.conj (e c) * x' = x' * MulAut.conj (e c) := by
    intro c hc
    rw [← hΦconj, ← hx, ← map_mul, ← map_mul, hc]
  obtain ⟨c, hcx, hcu⟩ := h (Φ.symm x') (Φ.symm u') (by rw [MulEquiv.orderOf_eq, hx'])
    (by rw [← map_pow, hu']) (E'.map Φ.symm.toMonoidHom)
    (fun w hw => by
      rw [mem_centralizer_singleton_iff]
      apply Φ.injective
      rw [map_mul, map_mul, hx]
      exact mem_centralizer_singleton_iff.mp (hE'x ((hmem E' w).mp hw)))
    (by rw [card_map_of_injective Φ.symm.injective]; exact hE'odd)
    (fun w hw => by
      rw [hmem, map_mul, map_mul, map_inv, hu]
      exact hE'u _ ((hmem E' w).mp hw))
    (fun c hc w hw => by
      rw [hmem, map_mul, map_mul, map_inv, hΦconj]
      exact hE'inn (e c) (hcomm c hc) _ ((hmem E' w).mp hw))
  refine ⟨e c, hcomm c hcx, fun hin => hcu ?_⟩
  have h1 := (hmem (E' ⊔ zpowers u') (MulAut.conj c * Φ.symm u' * (MulAut.conj c)⁻¹)).mpr
    (by rw [map_mul, map_mul, map_inv, hΦconj, hu]; exact hin)
  rw [Subgroup.map_sup, MonoidHom.map_zpowers] at h1
  exact h1

section OddNormal

variable {W : Type*} [Group W]

theorem exists_mem_mul_pow_eq_mul_pow {E T : Subgroup W}
    (hTE : ∀ τ ∈ T, ∀ e ∈ E, τ * e * τ⁻¹ ∈ E) {e τ : W} (he : e ∈ E) (hτ : τ ∈ T) (n : ℕ) :
    ∃ e' ∈ E, (e * τ) ^ n = e' * τ ^ n := by
  induction n with
  | zero => exact ⟨1, E.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨e', he', h⟩ := ih
    refine ⟨e' * (τ ^ n * e * (τ ^ n)⁻¹), E.mul_mem he' (hTE _ (T.pow_mem hτ n) e he), ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem mem_sup_zpowers_of_eq_mul [Finite W] {E T : Subgroup W} (hE : Odd (Nat.card E))
    (hT : IsPGroup 2 T) (hTcyc : IsCyclic T) (hTE : ∀ τ ∈ T, ∀ e ∈ E, τ * e * τ⁻¹ ∈ E)
    {u : W} (huT : u ∈ T) (hu : orderOf u = 4) {v e τ : W} (hv : v ^ 4 = 1) (he : e ∈ E)
    (hτ : τ ∈ T) (hve : v = e * τ) : v ∈ E ⊔ zpowers u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e', he', h⟩ := exists_mem_mul_pow_eq_mul_pow hTE he hτ 4
  rw [← hve, hv] at h
  have hτ4E : τ ^ 4 ∈ E := by
    rw [eq_inv_of_mul_eq_one_right h.symm]
    exact E.inv_mem he'
  have hτ4 : τ ^ 4 = 1 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨τ ^ 4, T.pow_mem hτ 4⟩
    rw [Subgroup.orderOf_mk] at hk
    have hdvd := Subgroup.orderOf_dvd_natCard E hτ4E
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr hE)
        (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans hdvd))
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  have hτu : τ ∈ zpowers u := mem_zpowers_of_orderOf_dvd_of_isCyclic hTcyc hτ huT
    (by rw [hu]; exact orderOf_dvd_of_pow_eq_one hτ4)
  rw [hve]
  exact mul_mem (mem_sup_left he) (mem_sup_right hτu)

end OddNormal

theorem not_hypothesisOneStar_of_full_conj {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hZ : center L = ⊥)
    (S : Sylow 2 (centralizer (L : Set G))) (hS : IsCyclic S) (hS4 : 4 ≤ Nat.card S)
    {g : G} (hg : g ∉ normalizer (L : Set G)) {T : Subgroup G}
    (hTg : T ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom)
    (hTN : T ≤ normalizer (L : Set G)) (hT : IsPGroup 2 T) (hTcard : Nat.card T = Nat.card S) :
    ¬ HypothesisOneStar (L ⧸ center L) := by
  classical
  intro hI
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmaxg : ∀ P : Subgroup G,
      P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom → IsPGroup 2 P →
      IsCyclic P ∧ Nat.card P ≤ Nat.card S :=
    fun P hPC hP => isCyclic_and_card_le_of_le_conj S hS hPC hP
  generalize Nat.card S = m at hS4 hTcard hmaxg
  clear hS S
  have hL' := hL
  obtain ⟨hq, -, hodd, hNC, -⟩ := hL'
  have : Group.IsPerfect L := ⟨hq.1⟩
  set C := centralizer (L : Set G) with hCdef
  set N := normalizer (L : Set G) with hNdef
  set Cg := C.map (MulAut.conj g).toMonoidHom with hCgdef
  have hgC : g ∉ normalizer (C : Set G) := by rwa [hNC]
  have hCCg : ∀ y ∈ C, y ∈ Cg → ∀ k : ℕ, orderOf y = 2 ^ k → y = 1 := by
    intro y hyC hyCg k hk
    have hdvd := Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_inf.mpr ⟨hyC, hyCg⟩)
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr (hodd g hgC))
        (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans hdvd))
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  have hT2 : ∀ y ∈ T, ∃ k : ℕ, orderOf y = 2 ^ k := fun y hy => by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨y, hy⟩
    exact ⟨k, by rwa [Subgroup.orderOf_mk] at hk⟩
  have hTC : ∀ y ∈ T, y ∈ C → y = 1 := fun y hyT hyC => by
    obtain ⟨k, hk⟩ := hT2 y hyT
    exact hCCg y hyC (hTg hyT) k hk
  have hTcyc : IsCyclic T := (hmaxg T hTg hT).1
  obtain ⟨⟨s, hsT⟩, hgen⟩ := IsCyclic.exists_generator (α := T)
  have hsord : orderOf s = m := by
    have h := orderOf_eq_card_of_forall_mem_zpowers hgen
    rwa [Subgroup.orderOf_mk, hTcard] at h
  have h4m : 4 ∣ m := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
    rw [hTcard] at hn
    have hn2 : 2 ≤ n := by
      by_contra h
      have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hn, show 4 = 2 ^ 2 by norm_num]
    exact Nat.pow_dvd_pow 2 hn2
  set u := s ^ (m / 4) with hudef
  have huT : u ∈ T := Subgroup.pow_mem _ hsT _
  have hu4 : orderOf u = 4 := by
    rw [hudef, orderOf_pow_of_dvd (by omega) (by rw [hsord]; exact Nat.div_dvd_of_dvd h4m), hsord]
    exact Nat.div_div_self h4m (by omega)
  set t := u ^ 2 with htdef
  have htT : t ∈ T := Subgroup.pow_mem _ huT 2
  have htN : t ∈ N := hTN htT
  have htord : orderOf t = 2 := by
    rw [htdef, orderOf_pow_of_dvd (by norm_num) (by rw [hu4]; norm_num), hu4]
  have htt : t * t = 1 := by rw [← sq, ← htord, pow_orderOf_eq_one]
  have htC : t ∉ C := fun h => by
    have := hTC t htT h
    rw [this, orderOf_one] at htord
    omega
  have hsTzp : ∀ y ∈ T, ∃ k : ℤ, s ^ k = y := by
    intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨y, hy⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := hsTzp a ha
    obtain ⟨j, rfl⟩ := hsTzp b hb
    exact (Commute.zpow_zpow_self s i j).eq
  set π := automizer L with hπdef
  have hπker : ∀ n : N, π n = 1 ↔ (n : G) ∈ C := fun n => automizer_eq_one_iff L n
  set tN : N := ⟨t, htN⟩ with htNdef
  set x := π tN with hxdef
  have hxord : orderOf x = 2 := by
    apply orderOf_eq_prime
    · rw [sq, ← map_mul]
      exact (hπker _).mpr (by
        change t * t ∈ C
        rw [htt]
        exact C.one_mem)
    · intro h
      exact htC ((hπker tN).mp h)
  set Q : Subgroup G := Cg ⊓ N ⊓ centralizer ({t} : Set G) with hQdef
  have hTQ : T ≤ Q := fun y hy => ⟨⟨hTg hy, hTN hy⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr (hTab y hy t htT)⟩
  have hQp : ∀ P : Subgroup G, P ≤ Q → IsPGroup 2 P → Nat.card P ≤ m :=
    fun P hPQ hP => (hmaxg P (hPQ.trans (inf_le_left.trans inf_le_left)) hP).2
  have hTQp : IsPGroup 2 (T.subgroupOf Q) := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTQ).symm
  obtain ⟨PQ, hPQ⟩ := hTQp.exists_le_sylow
  have hPQeq : (PQ : Subgroup Q) = T.subgroupOf Q := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hPQ
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTQ).toEquiv, hTcard]
    have h := hQp ((PQ : Subgroup Q).map Q.subtype) (Subgroup.map_subtype_le _)
      (PQ.isPGroup'.map _)
    rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective Q)] at h
  have hPQcyc : IsCyclic (PQ : Subgroup Q) := by
    rw [hPQeq]
    exact isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hTQ).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTQ).injective
  obtain ⟨EQ, -, ⟨hEQodd, -⟩, -, -, hEQmem, hEQmul, -, -⟩ :=
    CFSG.Semidihedral.Principal.cyclicSylowTwo_normal_odd_complement PQ hPQcyc
  set EG : Subgroup G := EQ.map Q.subtype with hEGdef
  have hEGQ : EG ≤ Q := Subgroup.map_subtype_le _
  have hEGodd : ∀ y ∈ EG, Odd (orderOf y) := by
    rintro _ ⟨y, hy, rfl⟩
    have := (hEQmem y).mp hy
    show Odd (orderOf (y : G))
    rw [Subgroup.orderOf_coe]
    exact this
  have hQsplit : ∀ y ∈ Q, ∃ e ∈ EG, ∃ τ ∈ T, y = e * τ := by
    intro y hy
    have h : (⟨y, hy⟩ : Q) ∈ (EQ : Set Q) * (PQ : Set Q) := by rw [hEQmul]; trivial
    obtain ⟨e, he, p, hp, hep⟩ := Set.mem_mul.mp h
    have hp' : p ∈ T.subgroupOf Q := by rw [← hPQeq]; exact hp
    refine ⟨e, ⟨e, he, rfl⟩, p, Subgroup.mem_subgroupOf.mp hp', ?_⟩
    have := congrArg Subtype.val hep
    simpa using this.symm
  have hnQ : ∀ n : N, (n : G) * t = t * n → ∀ y ∈ Q, (n : G) * y * (n : G)⁻¹ ∈ Q := by
    intro n hn y hy
    have hyt : y ∈ centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hy).2
    have hyCg : y ∈ Cg := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hy).1).1
    have hyN : y ∈ N := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hy).1).2
    have hnCg : (n : G) ∈ normalizer (Cg : Set G) :=
      mem_normalizer_conj_of_commute hL (by rw [htord]; exact even_two) (hTg htT) hn
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp hnCg y).mp hyCg,
        N.mul_mem (N.mul_mem n.2 hyN) (N.inv_mem n.2)⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hyt ⊢
    have hn' : (n : G)⁻¹ * t = t * (n : G)⁻¹ := by
      calc (n : G)⁻¹ * t = (n : G)⁻¹ * (t * n) * (n : G)⁻¹ := by group
        _ = (n : G)⁻¹ * ((n : G) * t) * (n : G)⁻¹ := by rw [hn]
        _ = t * (n : G)⁻¹ := by group
    calc (n : G) * y * (n : G)⁻¹ * t = (n : G) * y * ((n : G)⁻¹ * t) := by group
      _ = (n : G) * (y * t) * (n : G)⁻¹ := by rw [hn']; group
      _ = (n : G) * (t * y) * (n : G)⁻¹ := by rw [hyt]
      _ = t * ((n : G) * y * (n : G)⁻¹) := by rw [← mul_assoc, hn]; group
  have hnEG : ∀ n : N, (n : G) * t = t * n → ∀ y ∈ EG, (n : G) * y * (n : G)⁻¹ ∈ EG := by
    intro n hn y hy
    have hyQ := hEGQ hy
    have hconjQ := hnQ n hn y hyQ
    refine ⟨⟨_, hconjQ⟩, (hEQmem _).mpr ?_, rfl⟩
    rw [Subgroup.orderOf_mk]
    have h := hEGodd y hy
    rwa [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hEGN : EG ≤ N := hEGQ.trans (inf_le_left.trans inf_le_right)
  set Ebar : Subgroup (MulAut (L ⧸ center L)) := (EG.subgroupOf N).map π with hEbardef
  set Tbar : Subgroup (MulAut (L ⧸ center L)) := (T.subgroupOf N).map π with hTbardef
  have hEbarodd : Odd (Nat.card Ebar) := by
    have h1 : Odd (Nat.card EG) := by
      rw [hEGdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective Q)]
      exact hEQodd
    have h2 : Odd (Nat.card (EG.subgroupOf N)) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEGN).toEquiv]
    exact h2.of_dvd_nat (Subgroup.card_map_dvd _ _)
  have hTbarp : IsPGroup 2 Tbar :=
    (hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTN).symm).map π
  have huN : u ∈ N := hTN huT
  set uN : N := ⟨u, huN⟩ with huNdef
  have huN2 : uN ^ 2 = tN := Subtype.ext (by rw [Subgroup.coe_pow])
  have hπu2 : π uN ^ 2 = x := by rw [← map_pow, huN2]
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxord
    omega
  have huN4 : uN ^ 4 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hu4]
    exact pow_orderOf_eq_one u)
  have hπu4 : orderOf (π uN) = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := π uN)
      (by rw [pow_one, hπu2]; exact hx1)
      (by rw [show 2 ^ (1 + 1) = 4 by norm_num, ← map_pow, huN4, map_one])
    rw [h]
    norm_num
  have hπuT : π uN ∈ Tbar := ⟨uN, Subgroup.mem_subgroupOf.mpr huT, rfl⟩
  have hsN : s ∈ N := hTN hsT
  have hTbarz : Tbar = Subgroup.zpowers (π ⟨s, hsN⟩) := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, hk⟩ := hsTzp y (Subgroup.mem_subgroupOf.mp hy)
      have hyk : y = (⟨s, hsN⟩ : N) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
      rw [hyk, map_zpow]
      exact Subgroup.zpow_mem_zpowers _ k
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨s, hsN⟩, Subgroup.mem_subgroupOf.mpr hsT, rfl⟩
  have hTbarcyc : IsCyclic Tbar := by
    rw [hTbarz]
    exact Subgroup.isCyclic_zpowers _
  have hEbarx : Ebar ≤ centralizer ({x} : Set (MulAut (L ⧸ center L))) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff, hxdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hEGQ (mem_subgroupOf.mp hy)).2)
  have hnEbar : ∀ n : N, (n : G) * t = t * n → ∀ e ∈ Ebar, π n * e * (π n)⁻¹ ∈ Ebar := by
    rintro n hn _ ⟨y, hy, rfl⟩
    refine ⟨n * y * n⁻¹, mem_subgroupOf.mpr (hnEG n hn y (mem_subgroupOf.mp hy)), ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hTbarE : ∀ τ ∈ Tbar, ∀ e ∈ Ebar, τ * e * τ⁻¹ ∈ Ebar := by
    rintro _ ⟨y, hy, rfl⟩
    exact hnEbar y (hTab _ (mem_subgroupOf.mp hy) t htT)
  have hinn : ∀ c : L ⧸ center L, MulAut.conj c * x = x * MulAut.conj c →
      ∃ n : N, π n = MulAut.conj c ∧ (n : G) * t = t * n := by
    intro c hc
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective c
    set n : N := ⟨l, Subgroup.le_normalizer l.2⟩ with hndef
    have hπn : π n = MulAut.conj (l : L ⧸ center L) := by
      ext w
      obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective w
      rw [hπdef, automizer_apply_mk, MulAut.conj_apply]
      rfl
    refine ⟨n, hπn, ?_⟩
    rw [← hπn] at hc
    have hk1 : π (n * tN * n⁻¹ * tN⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hxdef, hc]
      group
    have hkC : (l : G) * t * (l : G)⁻¹ * t⁻¹ ∈ C := (hπker _).mp hk1
    have hkL : (l : G) * t * (l : G)⁻¹ * t⁻¹ ∈ L := by
      have h1 : t * (l : G)⁻¹ * t⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp htN _).mp (L.inv_mem l.2)
      have h2 := L.mul_mem l.2 h1
      simpa [mul_assoc] using h2
    have hkZ : (⟨_, hkL⟩ : L) ∈ center L := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hkC w w.2)
    rw [hZ, Subgroup.mem_bot] at hkZ
    have hk : (l : G) * t * (l : G)⁻¹ * t⁻¹ = 1 := congrArg Subtype.val hkZ
    calc (n : G) * t = ((l : G) * t * (l : G)⁻¹ * t⁻¹) * (t * l) := by
          rw [hndef]
          group
      _ = t * n := by rw [hk, one_mul]
  obtain ⟨c, hcx, hcu⟩ := hI x (π uN) hxord hπu2 Ebar hEbarx hEbarodd
    (hnEbar uN (hTab u huT t htT))
    (fun c hc e he => by
      obtain ⟨n, hnc, hnt⟩ := hinn c hc
      rw [← hnc]
      exact hnEbar n hnt e he)
  obtain ⟨n, hnc, hnt⟩ := hinn c hcx
  apply hcu
  rw [← hnc]
  obtain ⟨e, he, τ, hτ, hsplit⟩ := hQsplit _ (hnQ n hnt u (hTQ huT))
  have heN : e ∈ N := hEGN he
  have hτN : τ ∈ N := hTN hτ
  have hsplit' : n * uN * n⁻¹ = (⟨e, heN⟩ : N) * ⟨τ, hτN⟩ := Subtype.ext hsplit
  have hv : π n * π uN * (π n)⁻¹ = π ⟨e, heN⟩ * π ⟨τ, hτN⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul, hsplit', map_mul]
  have hv4 : (π n * π uN * (π n)⁻¹) ^ 4 = 1 := by
    rw [conj_pow, ← hπu4, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  exact mem_sup_zpowers_of_eq_mul hEbarodd hTbarp hTbarcyc hTbarE hπuT hπu4 hv4
    ⟨⟨e, heN⟩, mem_subgroupOf.mpr he, rfl⟩ ⟨⟨τ, hτN⟩, mem_subgroupOf.mpr hτ, rfl⟩ hv

variable {G : Type} [Group G] [Finite G]

theorem card_sylow_eq_two_of_standard_star {L : Subgroup G} (hset : StandardSetting G L)
    (hZ : center L = ⊥) (hI : HypothesisOneStar (L ⧸ center L))
    (S : Sylow 2 (centralizer (L : Set G))) : Nat.card S = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hset.isCyclic_sylow S
  have h2 : 2 ∣ Nat.card S := S.dvd_card_of_dvd_card (even_iff_two_dvd.mp hset.standard.2.1)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
  by_contra hne
  have hS4 : 4 ≤ Nat.card S := by
    rw [hn] at h2 hne ⊢
    rcases n with _ | _ | n
    · norm_num at h2
    · norm_num at hne
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_cases hall : ∀ g : G, g ∉ normalizer (L : Set G) → ∀ P : Subgroup G,
      P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓ normalizer (L : Set G) →
      IsPGroup 2 P → Nat.card P ≤ 2
  · exact hset.false_of_forall_card_le_two
      (CFSG.SeitzReduction.foursGroupCondition_of_isStandard hset.standard hZ) S hS4 hall
  · push Not at hall
    obtain ⟨g, hg, P, hP, hP2, hPcard⟩ := hall
    have hP4 : 4 ≤ Nat.card P := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
      rw [hk] at hPcard ⊢
      rcases k with _ | _ | k
      · norm_num at hPcard
      · norm_num at hPcard
      · calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨g', hg', -, T, -, -, -, hTg, hTN, hT, hTcard, -⟩ :=
      exists_full_conj_centralized hset.standard S hS hg (hP.trans inf_le_left)
        (hP.trans inf_le_right) hP2 hP4
    exact not_hypothesisOneStar_of_full_conj hset.standard hZ S hS hS4 hg' hTg hTN hT hTcard hI

theorem inf_centralizer_eq_zpowers_of_standard_star {L : Subgroup G}
    (hset : StandardSetting G L) (hZ : center L = ⊥) (hI : HypothesisOneStar (L ⧸ center L))
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tC : centralizer (L : Set G) := ⟨t, htC⟩ with htCdef
  have htC2 : orderOf tC = 2 := by rw [htCdef, orderOf_mk, ht]
  have hp : IsPGroup 2 (zpowers tC) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htC2, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have htS : tC ∈ (S : Subgroup (centralizer (L : Set G))) := hS (mem_zpowers tC)
  obtain ⟨-, -, -, -, -, -, hCH, -, -⟩ :=
    CFSG.ComponentClassification.StandardRecognition.standard_cyclic_local_centralizer_kernel
      hset.standard S (hset.isCyclic_sylow S) htS htC2 (hset.core t ht)
  have hSeq : (S : Subgroup (centralizer (L : Set G))) = zpowers tC :=
    (eq_of_le_of_card_ge hS (by
      rw [card_sylow_eq_two_of_standard_star hset hZ hI S, Nat.card_zpowers, htC2])).symm
  rw [hCH, hSeq, MonoidHom.map_zpowers]
  rfl

end CFSG.SeitzReduction.RankOne
