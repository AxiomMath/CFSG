module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigRestrict
public import CFSG.Milestones.CL_LIT_Aschbacher_proper_two_generated_core
public import CFSG.GH74.Uniqueness.SU.KI6Janko

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

private theorem exists_mem_ne_ne_aux' {X : Type} [Group X] [Finite X] {H : Subgroup X}
    (h : 2 < Nat.card H) (x y : X) : ∃ z ∈ H, z ≠ x ∧ z ≠ y := by
  by_contra hc
  have hsub : (H : Set X) ⊆ {x, y} := fun z hz => by
    by_cases hzx : z = x
    · exact Or.inl hzx
    · by_cases hzy : z = y
      · exact Or.inr hzy
      · exact (hc ⟨z, hz, hzx, hzy⟩).elim
  have hle : Nat.card H ≤ 2 := by
    have e : Nat.card H = (H : Set X).ncard := Nat.card_coe_set_eq (H : Set X)
    rw [e]
    calc (H : Set X).ncard ≤ ({x, y} : Set X).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({y} : Set X).ncard + 1 := Set.ncard_insert_le x {y}
      _ = 2 := by rw [Set.ncard_singleton]
  omega

theorem two_le_pRank_of_two_le_pRank_map {X : Type} [Group X] [Finite X] {Z : Subgroup X}
    [Z.Normal] (hZc : Z ≤ center X) (hZ2 : IsPGroup 2 Z) (hZ : Nat.card Z ≠ 2)
    {P : Subgroup X} (hZP : Z ≤ P) (hP : 2 ≤ CFSG.Open.pRank 2 (P.map (QuotientGroup.mk' Z))) :
    2 ≤ CFSG.Open.pRank 2 P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' Z with hπ
  have hcen : ∀ z ∈ Z, ∀ g : X, z * g = g * z := fun z hz g =>
    (mem_center_iff.mp (hZc hz) g).symm
  have hker : ∀ g : X, π g = 1 ↔ g ∈ Z := fun g => QuotientGroup.eq_one_iff g
  have hfour : ∀ u v : X, u ∈ P → v ∈ P → u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 → u ≠ v →
      u * v = v * u → 2 ≤ CFSG.Open.pRank 2 P := by
    intro u v huP hvP hu hv hu1 hv1 huv hc
    obtain ⟨V, hVP, hV, -, -⟩ := GorensteinWalter.exists_kleinFour_of_commuting_involutions_le P
      u v ⟨hu1, by rw [sq]; exact hu⟩ ⟨hv1, by rw [sq]; exact hv⟩ huv hc huP hvP
    exact SectionRank.le_pRank (by norm_num) hVP (isElemAbelian_of_isKleinFour hV)
      (by rw [hV.card_four]; norm_num)
  obtain ⟨Eb, hEbP, hEb, hEbc⟩ :=
    SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) (k := 2) hP
  have hEbK : IsKleinFour Eb :=
    FooteLit.isKleinFour_of_card_eq_four (by rw [hEbc]; norm_num) hEb.2
  obtain ⟨xb, hxb, hxb1, -⟩ :=
    exists_mem_ne_ne_aux' (H := Eb) (by rw [hEbK.card_four]; norm_num) 1 1
  obtain ⟨yb, hyb, hyb1, hyx⟩ :=
    exists_mem_ne_ne_aux' (H := Eb) (by rw [hEbK.card_four]; norm_num) 1 xb
  have hsqb : ∀ w ∈ Eb, w * w = 1 := fun w hw => by rw [← sq]; exact hEb.2 w hw
  obtain ⟨x, hxP, rfl⟩ := hEbP hxb
  obtain ⟨y, hyP, rfl⟩ := hEbP hyb
  have hxZ : x ∉ Z := fun h => hxb1 ((hker x).mpr h)
  have hyZ : y ∉ Z := fun h => hyb1 ((hker y).mpr h)
  have hxyZ : x * y ∉ Z := fun h => by
    have h1 : π x * π y = 1 := by rw [← map_mul]; exact (hker _).mpr h
    apply hyx
    have hxi : (π x)⁻¹ = π x := inv_eq_of_mul_eq_one_right (hsqb _ hxb)
    rw [← hxi]
    exact eq_inv_of_mul_eq_one_right h1
  have hx2 : x * x ∈ Z := (hker _).mp (by rw [map_mul]; exact hsqb _ hxb)
  have hy2 : y * y ∈ Z := (hker _).mp (by rw [map_mul]; exact hsqb _ hyb)
  set c := x⁻¹ * y⁻¹ * x * y with hcdef
  have hcZ : c ∈ Z := (hker _).mp (by
    have hc := comm_of_isKleinFour hEbK _ hxb _ hyb
    rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv,
      show (π x)⁻¹ * (π y)⁻¹ * π x * π y = (π x)⁻¹ * (π y)⁻¹ * (π x * π y) by group, hc]
    group)
  have hcc : c * c = 1 := by
    have h1 : y⁻¹ * (x * x) * y = x * x := by
      rw [mul_assoc, hcen _ hx2 y]
      group
    have h2 : y⁻¹ * (x * x) * y = x * x * (c * c) := by
      have e1 : y⁻¹ * (x * x) * y = x * (c * x) * c := by rw [hcdef]; group
      rw [e1, hcen c hcZ x]
      group
    have h3 : x * x * (c * c) = x * x * 1 := by rw [← h2, h1, mul_one]
    exact mul_left_cancel h3
  have hxy2 : x * y * (x * y) = x * x * (y * y) * c⁻¹ := by
    have hyx' : y * x = x * y * c⁻¹ := by rw [hcdef]; group
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y * c⁻¹) * y := by rw [hyx']
      _ = x * x * y * (c⁻¹ * y) := by group
      _ = x * x * y * (y * c⁻¹) := by rw [hcen _ (inv_mem hcZ) y]
      _ = x * x * (y * y) * c⁻¹ := by group
  by_cases hZb : Z = ⊥
  · have hx2' : x * x = 1 := by rw [hZb] at hx2; exact mem_bot.mp hx2
    have hy2' : y * y = 1 := by rw [hZb] at hy2; exact mem_bot.mp hy2
    have hc1 : c = 1 := by rw [hZb] at hcZ; exact mem_bot.mp hcZ
    refine hfour x y hxP hyP hx2' hy2' (fun h => hxZ (h ▸ one_mem _))
      (fun h => hyZ (h ▸ one_mem _)) (fun h => hyx (by rw [h])) ?_
    have e : x * y = y * x * c := by rw [hcdef]; group
    rw [e, hc1, mul_one]
  by_cases h2inv : ∃ z₁ ∈ Z, ∃ z₂ ∈ Z, z₁ * z₁ = 1 ∧ z₂ * z₂ = 1 ∧ z₁ ≠ 1 ∧ z₂ ≠ 1 ∧ z₁ ≠ z₂
  · obtain ⟨z₁, hz₁, z₂, hz₂, h1, h2, h11, h21, h12⟩ := h2inv
    exact hfour z₁ z₂ (hZP hz₁) (hZP hz₂) h1 h2 h11 h21 h12 (hcen z₁ hz₁ z₂)
  have huniq : ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, z₁ * z₁ = 1 → z₂ * z₂ = 1 → z₁ ≠ 1 → z₂ ≠ 1 → z₁ = z₂ :=
    fun z₁ hz₁ z₂ hz₂ h1 h2 h11 h21 => by
      by_contra h12
      exact h2inv ⟨z₁, hz₁, z₂, hz₂, h1, h2, h11, h21, h12⟩
  have hZnt : Nontrivial Z := (Subgroup.nontrivial_iff_ne_bot Z).mpr hZb
  obtain ⟨n, hn⟩ := hZ2.exists_card_eq
  have hZ4 : 4 ≤ Nat.card Z := by
    have h1 : 1 < Nat.card Z := Finite.one_lt_card_iff_nontrivial.mpr hZnt
    rw [hn] at h1 hZ ⊢
    rcases n with _ | _ | n
    · norm_num at h1
    · norm_num at hZ
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨z₀', hz₀'⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2
    (by rw [hn]; exact dvd_pow_self 2 (by rintro rfl; rw [hn] at hZ4; norm_num at hZ4))
  set z₀ : X := z₀'.1 with hz₀def
  have hz₀Z : z₀ ∈ Z := z₀'.2
  have hz₀2 : z₀ * z₀ = 1 := by
    have h := pow_orderOf_eq_one z₀'
    rw [hz₀', sq] at h
    exact congrArg Subtype.val h
  have hz₀1 : z₀ ≠ 1 := fun h => by
    have h' : z₀' = 1 := Subtype.ext h
    rw [h', orderOf_one] at hz₀'
    norm_num at hz₀'
  let φ : ↥Z →* ↥Z := MonoidHom.mk' (fun z => z * z) (fun a b => Subtype.ext (by
    show (a : X) * b * (a * b) = a * a * (b * b)
    calc (a : X) * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hcen _ b.2 a]
      _ = a * a * (b * b) := by group))
  have hkerφ : Nat.card φ.ker = 2 := by
    apply le_antisymm
    · by_contra hlt
      obtain ⟨w, hw, hw1, hwz⟩ := exists_mem_ne_ne_aux' (H := φ.ker) (by omega) 1 ⟨z₀, hz₀Z⟩
      have hw2 : (w : X) * w = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hw)
      have hw1' : (w : X) ≠ 1 := fun h => hw1 (Subtype.ext h)
      exact hwz (Subtype.ext (huniq _ w.2 _ hz₀Z hw2 hz₀2 hw1' hz₀1))
    · have h1 : (⟨z₀, hz₀Z⟩ : ↥Z) ∈ φ.ker := MonoidHom.mem_ker.mpr (Subtype.ext hz₀2)
      have : Nontrivial φ.ker := (Subgroup.nontrivial_iff_exists_ne_one _).mpr
        ⟨_, h1, fun h => hz₀1 (congrArg Subtype.val h)⟩
      exact Finite.one_lt_card_iff_nontrivial.mpr this
  have hcardZ : Nat.card ↥Z = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hindex : φ.range.index = 2 := by
    have h1 := Subgroup.card_mul_index φ.range
    rw [hcardZ, hkerφ] at h1
    have hpos : 0 < Nat.card φ.range := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have hz₀sq : (⟨z₀, hz₀Z⟩ : ↥Z) ∈ φ.range := by
    have h2 : 2 ∣ Nat.card φ.range := by
      have h1 : Nat.card φ.range * 2 = Nat.card ↥Z := by rw [hcardZ, hkerφ]
      obtain ⟨k, hk⟩ := (hZ2.to_subgroup φ.range).exists_card_eq
      rw [hk] at h1 ⊢
      rcases k with _ | k
      · norm_num at h1
        omega
      · exact dvd_pow_self 2 (Nat.succ_ne_zero k)
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := φ.range) 2 h2
    have hw2 : ((w : ↥Z) : X) * (w : ↥Z) = 1 := by
      have h := pow_orderOf_eq_one w
      rw [hw, sq] at h
      exact congrArg (fun v : φ.range => ((v : ↥Z) : X)) h
    have hw1 : ((w : ↥Z) : X) ≠ 1 := fun h => by
      have hw1' : w = 1 := Subtype.ext (Subtype.ext h)
      rw [hw1', orderOf_one] at hw
      norm_num at hw
    have heq : ((w : ↥Z) : X) = z₀ := huniq _ (w : ↥Z).2 _ hz₀Z hw2 hz₀2 hw1 hz₀1
    have : (w : ↥Z) = ⟨z₀, hz₀Z⟩ := Subtype.ext heq
    rw [← this]
    exact w.2
  have hcsq : (⟨c⁻¹, inv_mem hcZ⟩ : ↥Z) ∈ φ.range := by
    by_cases hc1 : c = 1
    · have : (⟨c⁻¹, inv_mem hcZ⟩ : ↥Z) = 1 := Subtype.ext (by simp [hc1])
      rw [this]
      exact one_mem _
    · have hcz : c = z₀ := huniq _ hcZ _ hz₀Z hcc hz₀2 hc1 hz₀1
      have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
      have : (⟨c⁻¹, inv_mem hcZ⟩ : ↥Z) = ⟨z₀, hz₀Z⟩ := Subtype.ext (by
        show c⁻¹ = z₀
        rw [hci, hcz])
      rw [this]
      exact hz₀sq
  have hsq : ∀ w : X, w ∈ P → w ∉ Z → ∀ hw : w * w ∈ Z, (⟨w * w, hw⟩ : ↥Z) ∈ φ.range →
      2 ≤ CFSG.Open.pRank 2 P := by
    intro w hwP hwZ hw hwr
    obtain ⟨d, hd⟩ := hwr
    have hd' : (d : X) * d = w * w := congrArg Subtype.val hd
    have hdc : ∀ g : X, (d : X)⁻¹ * g = g * (d : X)⁻¹ := hcen _ (inv_mem d.2)
    have hu : w * (d : X)⁻¹ * (w * (d : X)⁻¹) = 1 := by
      calc w * (d : X)⁻¹ * (w * (d : X)⁻¹) = w * ((d : X)⁻¹ * w) * (d : X)⁻¹ := by group
        _ = w * (w * (d : X)⁻¹) * (d : X)⁻¹ := by rw [hdc w]
        _ = w * w * ((d : X) * d)⁻¹ := by group
        _ = 1 := by rw [hd', mul_inv_cancel]
    have huZ : w * (d : X)⁻¹ ∉ Z := fun h => hwZ (by
      have e : w = w * (d : X)⁻¹ * d := by group
      rw [e]
      exact mul_mem h d.2)
    refine hfour _ z₀ (mul_mem hwP (hZP (inv_mem d.2))) (hZP hz₀Z) hu hz₀2
      (fun h => huZ (h ▸ one_mem _)) hz₀1 (fun h => huZ (h ▸ hz₀Z)) ?_
    exact (hcen z₀ hz₀Z _).symm
  by_cases hxs : (⟨x * x, hx2⟩ : ↥Z) ∈ φ.range
  · exact hsq x hxP hxZ hx2 hxs
  by_cases hys : (⟨y * y, hy2⟩ : ↥Z) ∈ φ.range
  · exact hsq y hyP hyZ hy2 hys
  have hxy : (⟨x * x, hx2⟩ : ↥Z) * ⟨y * y, hy2⟩ ∈ φ.range :=
    (Subgroup.mul_mem_iff_of_index_two hindex).mpr (iff_of_false hxs hys)
  have hxy2Z : x * y * (x * y) ∈ Z := by
    rw [hxy2]
    exact mul_mem (mul_mem hx2 hy2) (inv_mem hcZ)
  refine hsq (x * y) (mul_mem hxP hyP) hxyZ hxy2Z ?_
  have e : (⟨x * y * (x * y), hxy2Z⟩ : ↥Z) =
      (⟨x * x, hx2⟩ : ↥Z) * ⟨y * y, hy2⟩ * ⟨c⁻¹, inv_mem hcZ⟩ := Subtype.ext hxy2
  rw [e]
  exact mul_mem hxy hcsq

theorem gamma_eq_top_of_gamma_map_eq_top' {X : Type} [Group X] [Finite X] {Z : Subgroup X}
    [Z.Normal] (hZ2 : IsPGroup 2 Z)
    (hpre : ∀ P : Subgroup X, Z ≤ P →
      2 ≤ CFSG.Open.pRank 2 (P.map (QuotientGroup.mk' Z)) → 2 ≤ CFSG.Open.pRank 2 P)
    (T : Sylow 2 X) (hT : 2 ≤ CFSG.Open.pRank 2 (T : Subgroup X))
    (hΓ : CFSG.Open.properTwoGenCoreGamma ((T : Subgroup X).map (QuotientGroup.mk' Z)) 2 = ⊤) :
    CFSG.Open.properTwoGenCoreGamma (T : Subgroup X) 2 = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' Z with hπ
  set Γ := CFSG.Open.properTwoGenCoreGamma (T : Subgroup X) 2 with hΓdef
  have hZT : Z ≤ T := hZ2.le_sylow_of_normal T
  have hTΓ : (T : Subgroup X) ≤ Γ := CFSG.ProperTwoGeneratedCore.sylow_le_gamma T hT
  have hle : CFSG.Open.properTwoGenCoreGamma ((T : Subgroup X).map π) 2 ≤ Γ.map π := by
    refine (CFSG.ProperTwoGeneratedCore.gamma_le_iff _ _ 2).mpr fun Qb hQbT hQb gb hgb => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z gb
    set Q := Qb.comap π with hQdef
    have hZQ : Z ≤ Q := fun z hz => by
      show π z ∈ Qb
      have h1 : π z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
      rw [h1]
      exact one_mem _
    have hQT : Q ≤ T := by
      intro q hq
      obtain ⟨t, htT, htq⟩ := hQbT hq
      have h1 : t⁻¹ * q ∈ Z := QuotientGroup.eq.mp htq
      have e : q = t * (t⁻¹ * q) := by group
      rw [e]
      exact mul_mem htT (hZT h1)
    have hQmap : Q.map π = Qb := Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective Z) Qb
    have hQr : 2 ≤ CFSG.Open.pRank 2 Q := hpre Q hZQ (by rw [hQmap]; exact hQb)
    have hgQ : g ∈ normalizer (Q : Set X) := by
      rw [mem_normalizer_iff]
      intro x
      show π x ∈ Qb ↔ π (g * x * g⁻¹) ∈ Qb
      rw [map_mul, map_mul, map_inv]
      exact mem_normalizer_iff.mp hgb (π x)
    exact ⟨g, (CFSG.ProperTwoGeneratedCore.gamma_le_iff _ Γ 2).mp le_rfl Q hQT hQr hgQ, rfl⟩
  have hmap : Γ.map π = ⊤ := top_le_iff.mp (by rw [← hΓ]; exact hle)
  have hcomap := Subgroup.comap_map_eq π Γ
  rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr (hZT.trans hTΓ)] at hcomap
  exact hcomap.symm

@[expose] def QuasisimpleBigCenterRankThree : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → pPrimeCore 2 J = ⊥ →
    Blueprint.Catalog (J ⧸ center J) → 4 ≤ Nat.card (center J) →
      3 ≤ CFSG.Open.twoRank (J ⧸ center J)

section Certified

theorem gamma_eq_top_of_not_isSolomonI (hBig : QuasisimpleBigCenterRankThree) {X : Type}
    [Group X] [Finite X] (hXq : IsQuasisimple X) (hXO : pPrimeCore 2 X = ⊥)
    (hXcat : Blueprint.Catalog (X ⧸ center X)) (hZ2 : IsPGroup 2 (center X))
    (h3 : 3 ≤ CFSG.Open.twoRank X) (hI : ¬ IsSolomonI X) (T : Sylow 2 X) :
    CFSG.Open.properTwoGenCoreGamma (T : Subgroup X) 2 = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXs : IsSimpleGroup (X ⧸ center X) := hXq.2.1
  have hT3 : 3 ≤ CFSG.Open.pRank 2 (T : Subgroup X) := by
    rw [CFSG.ProperTwoGeneratedCore.sylow_two_rank_eq T]
    exact h3
  by_contra hΓ
  by_cases hZ : Nat.card (center X) = 2
  ·
    have hqpcc := CFSG.GH74.Uniqueness.SU.K.R6.quasisimpleProperCoreClassification_all X hXq.1
      hXs hZ (by omega) T _ (CFSG.ProperTwoGeneratedCore.sylow_le_gamma T (by omega)) hΓ le_rfl
    apply hI
    rcases hqpcc with e | e
    · exact Or.inr (Or.inr (Or.inr ⟨e, hZ⟩))
    · exact Or.inr (Or.inr (Or.inl (CFSG.Open.fusionIsBenderGroup_of_isBenderGroup
        (CFSG.BenderSuzuki.IsBenderGroup.isSuzuki 1 le_rfl e.some))))
  set π := QuotientGroup.mk' (center X) with hπ
  set Tb : Sylow 2 (X ⧸ center X) := T.mapSurjective (QuotientGroup.mk'_surjective (center X))
  have hΓb : CFSG.Open.properTwoGenCoreGamma (Tb : Subgroup (X ⧸ center X)) 2 ≠ ⊤ := fun h =>
    hΓ (gamma_eq_top_of_gamma_map_eq_top' hZ2
      (fun P hZP hP => two_le_pRank_of_two_le_pRank_map le_rfl hZ2 hZ hZP hP) T (by omega) h)
  have h3b : 3 ≤ CFSG.Open.twoRank (X ⧸ center X) := by
    by_cases hZb : center X = ⊥
    · have e : X ⧸ center X ≃* X :=
        (QuotientGroup.quotientMulEquivOfEq hZb).trans QuotientGroup.quotientBot
      rw [CFSG.Open.twoRank, SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
      exact h3
    · refine hBig X hXq hXO hXcat ?_
      obtain ⟨n, hn⟩ := hZ2.exists_card_eq
      have h1 : 1 < Nat.card (center X) :=
        Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot _).mpr hZb)
      rw [hn] at h1 hZ ⊢
      rcases n with _ | _ | n
      · norm_num at h1
      · norm_num at hZ
      · calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hTb3 : 3 ≤ CFSG.Open.pRank 2 (Tb : Subgroup (X ⧸ center X)) := by
    rw [CFSG.ProperTwoGeneratedCore.sylow_two_rank_eq Tb]
    exact h3b
  apply hI
  rcases CFSG.Milestones.cl_lit_aschbacher_proper_two_generated_core (X ⧸ center X) hXq.2.2 Tb
      hTb3 hΓb with hΓ1 | e
  · exact Or.inr (Or.inr (Or.inl (CFSG.Open.fusionIsBenderGroup_of_isBenderGroup
      (CFSG.ProperTwoGeneratedCore.Lemma37.CyclicCase.isBenderGroup_of_gamma_one_ne_top Tb
        (by omega) hΓ1))))
  · exact Or.inl e

end Certified

end CFSG.ComponentClassification.Sol76.Sig
