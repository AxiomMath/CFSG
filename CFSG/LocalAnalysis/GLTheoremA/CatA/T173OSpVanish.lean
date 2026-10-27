module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpTorus3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open CFSG.RankThree.Classical (spEnd spEnd_apply spLin spLin_injective)
open CFSG.RankThree.PartOne.KCSpFull (spEnd_mul spEnd_one)
open CFSG.LieType.SeitzGeneration.RootPair
open CFSG.StandardType.TableBSymp
open CFSG.LocalAnalysis.GLTheoremA.T173X

variable {F : Type} [Field F] [Finite F] [CharP F 2] {ℓ n p : ℕ}

private def commonFixed (T : Subgroup ↥(StatedSp ℓ F)) :
    Submodule F (Fin ℓ ⊕ Fin ℓ → F) where
  carrier := {v | ∀ t ∈ T, spEnd t v = v}
  zero_mem' := fun t _ => map_zero _
  add_mem' := fun hv hw t ht => by
    show spEnd t (_ + _) = _
    rw [map_add, hv t ht, hw t ht]
  smul_mem' := fun c v hv t ht => by
    show spEnd t (c • v) = c • v
    rw [map_smul, hv t ht]

private theorem mem_commonFixed {T : Subgroup ↥(StatedSp ℓ F)}
    {v : Fin ℓ ⊕ Fin ℓ → F} :
    v ∈ commonFixed T ↔ ∀ t ∈ T, spEnd t v = v := Iff.rfl

private theorem exists_ne_zero_mem_commonFixed {T : Subgroup ↥(StatedSp ℓ F)}
    (hT2 : IsPGroup 2 T) (hℓ : 1 ≤ ℓ) (hn : Nat.card F = 2 ^ n) :
    ∃ v, v ≠ 0 ∧ v ∈ commonFixed T := by
  classical
  let ρ : ↥T →* Module.End F (Fin ℓ ⊕ Fin ℓ → F) :=
    { toFun := fun t => spEnd (t : ↥(StatedSp ℓ F))
      map_one' := by rw [Subgroup.coe_one, spEnd_one]
      map_mul' := fun a b => by rw [Subgroup.coe_mul, spEnd_mul] }
  letI : MulAction ↥T (Fin ℓ ⊕ Fin ℓ → F) :=
    { smul := fun t v => ρ t v
      one_smul := fun v => by
        change spEnd ((1 : ↥T) : ↥(StatedSp ℓ F)) v = v
        rw [Subgroup.coe_one, spEnd_one]
        rfl
      mul_smul := fun a b v => by
        change spEnd (((a * b : ↥T) : ↥(StatedSp ℓ F))) v =
          spEnd ((a : ↥T) : ↥(StatedSp ℓ F)) (spEnd ((b : ↥T) : ↥(StatedSp ℓ F)) v)
        rw [Subgroup.coe_mul, spEnd_mul, Module.End.mul_apply] }
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardα : Nat.card (Fin ℓ ⊕ Fin ℓ) = 2 * ℓ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hcard : 2 ∣ Nat.card (Fin ℓ ⊕ Fin ℓ → F) := by
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      have h1 := Finite.one_lt_card (α := F)
      omega
    have h2 : 2 ∣ 2 ^ n := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      rw [pow_succ]
      exact ⟨2 ^ m, by ring⟩
    rw [Nat.card_fun, hn, hcardα]
    exact dvd_pow h2 (by omega)
  have hfix0 : (0 : Fin ℓ ⊕ Fin ℓ → F) ∈ MulAction.fixedPoints ↥T (Fin ℓ ⊕ Fin ℓ → F) :=
    fun t => map_zero _
  obtain ⟨v, hv, hne⟩ := hT2.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (Fin ℓ ⊕ Fin ℓ → F) hcard hfix0
  exact ⟨v, hne.symm, fun t ht => hv ⟨t, ht⟩⟩

private theorem commonFixed_normalizer_maps {T : Subgroup ↥(StatedSp ℓ F)}
    {g : ↥(StatedSp ℓ F)} (hg : g ∈ Subgroup.normalizer (T : Set ↥(StatedSp ℓ F)))
    {v : Fin ℓ ⊕ Fin ℓ → F} (hv : v ∈ commonFixed T) :
    spEnd g v ∈ commonFixed T := by
  rw [mem_commonFixed] at hv ⊢
  intro t ht
  have hgt : g⁻¹ * t * g ∈ T :=
    ((Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg)) t).mp ht
  calc spEnd t (spEnd g v) = spEnd (t * g) v := by rw [spEnd_mul]; rfl
    _ = spEnd (g * (g⁻¹ * t * g)) v := by
        rw [show g * (g⁻¹ * t * g) = t * g by group]
    _ = spEnd g (spEnd (g⁻¹ * t * g) v) := by rw [spEnd_mul]; rfl
    _ = spEnd g v := by rw [hv _ hgt]

private theorem not_commutative_of_isComponentOf {G : Type} [Group G] {K L : Subgroup G}
    (hK : IsComponentOf K L) (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) : False := by
  have hperf : Group.IsPerfect ↥K := Group.isPerfect_def.mpr hK.2.2.1
  haveI : Nontrivial ↥K := by
    haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2.2.2
    exact (QuotientGroup.mk'_surjective (Subgroup.center ↥K)).nontrivial
  haveI : IsMulCommutative ↥K :=
    isMulCommutative_iff.mpr fun a b => Subtype.ext (hcomm a a.2 b b.2)
  haveI : Group.IsPerfect ↥K := hperf
  exact (Group.IsPerfect.not_isMulCommutative (G := ↥K)) inferInstance

private theorem diagSp_mulSingle_mem_inf
    {V K : Subgroup ↥(StatedSp ℓ F)}
    (hV : V = CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p)
    (hpl : ∀ k ∈ K, ∀ i, spEnd k (Pi.single (Sum.inl i) (1 : F)) ∈ stdPlane F ℓ i ∧
      spEnd k (Pi.single (Sum.inr i) (1 : F)) ∈ stdPlane F ℓ i)
    {i : Fin ℓ} {ζ : Fˣ} (hζp : ζ ^ p = 1)
    (hfix : ∀ k ∈ K, spEnd k (Pi.single (Sum.inl i) (1 : F)) = Pi.single (Sum.inl i) 1 ∧
      spEnd k (Pi.single (Sum.inr i) (1 : F)) = Pi.single (Sum.inr i) 1) :
    diagSp F ℓ (Pi.mulSingle i ζ) ∈
      V ⊓ Subgroup.centralizer (K : Set ↥(StatedSp ℓ F)) := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [hV]
    refine (CFSG.LocalAnalysis.GLTheoremA.Y10F.mem_symplecticQTorus (F := F) (ℓ := ℓ)).2
      ⟨Pi.mulSingle i ζ, fun j => ?_, rfl⟩
    by_cases hj : j = i
    · subst hj; rw [Pi.mulSingle_eq_same, hζp]
    · rw [Pi.mulSingle_eq_of_ne hj, one_pow]
  · exact diagSp_mem_centralizer_of_fixes hpl
      (I := {i}) (fun k hk i' hi => by
        rw [Set.mem_singleton_iff.mp hi]; exact hfix k hk) (fun j hj => by
        rw [Pi.mulSingle_eq_of_ne (by simpa using hj)])

private theorem not_two_ne_one_of_preserves_planes
    (hp : p.Prime) (hn : Nat.card F = 2 ^ n) (hpq : p ∣ 2 ^ n - 1)
    {V K : Subgroup ↥(StatedSp ℓ F)}
    (hV : V = CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p)
    {t : Fin ℓ → Fˣ} (htp : ∀ i, t i ^ p = 1)
    (hKp : ⁅K, K⁆ = K)
    (hKc : K ≤ Subgroup.centralizer ({diagSp F ℓ t} : Set ↥(StatedSp ℓ F)))
    (hpl : ∀ k ∈ K, ∀ i, spEnd k (Pi.single (Sum.inl i) (1 : F)) ∈ stdPlane F ℓ i ∧
      spEnd k (Pi.single (Sum.inr i) (1 : F)) ∈ stdPlane F ℓ i)
    (hcent : V ⊓ Subgroup.centralizer (K : Set ↥(StatedSp ℓ F)) =
      Subgroup.zpowers (diagSp F ℓ t))
    {i₁ i₂ : Fin ℓ} (hne : i₁ ≠ i₂) (h1 : t i₁ ≠ 1) (h2 : t i₂ ≠ 1) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpdvd : p ∣ Nat.card Fˣ := by rw [Nat.card_units, hn]; exact hpq
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hζp : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    intro h
    exact hp.ne_one (by rw [← hζo]; exact orderOf_eq_one_iff.mpr h)
  have hfix1 := fixes_plane_of_perfect hKp hKc hpl h1
  have hfix2 := fixes_plane_of_perfect hKp hKc hpl h2
  have hmem₁ := diagSp_mulSingle_mem_inf hV hpl hζp hfix1
  rw [hcent] at hmem₁
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem₁
  have hk2 : t i₂ ^ k = 1 := by
    have hsk : t ^ k = Pi.mulSingle i₁ ζ := diagSp_injective (by rw [map_zpow, hk])
    simpa [Pi.mulSingle_eq_of_ne (Ne.symm hne)] using congrFun hsk i₂
  have hmem₂ := diagSp_mulSingle_mem_inf hV hpl hζp hfix2
  rw [hcent] at hmem₂
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem₂
  have hm1 : t i₁ ^ m = 1 := by
    have hsm : t ^ m = Pi.mulSingle i₂ ζ := diagSp_injective (by rw [map_zpow, hm])
    simpa [Pi.mulSingle_eq_of_ne hne] using congrFun hsm i₁
  have hord : orderOf (t i₁) = p := orderOf_eq_prime (htp i₁) h1
  have hpm : (p : ℤ) ∣ m := by
    have hdvd : ((orderOf (t i₁) : ℕ) : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.mpr hm1
    simpa [hord] using hdvd
  obtain ⟨c, rfl⟩ := hpm
  have hzero : t i₂ ^ ((p : ℤ) * c) = 1 := by
    rw [zpow_mul, zpow_natCast, htp i₂, one_zpow]
  have hζeq : ζ = 1 := by
    have hsm : t ^ ((p : ℤ) * c) = Pi.mulSingle i₂ ζ := by
      apply diagSp_injective
      rw [map_zpow]
      exact hm
    have h := congrFun hsm i₂
    simpa [Pi.mulSingle_eq_same, hzero] using h.symm
  exact hζ1 hζeq

private theorem four_le_card_of_prime_dvd (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : Nat.card F = 2 ^ n) (hpq : p ∣ 2 ^ n - 1) : 4 ≤ Nat.card F := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  have hn1 : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    have hn' : Nat.card F = 2 ^ n := hn
    rw [h0, pow_zero] at hn'
    have h1 := Finite.one_lt_card (α := F)
    omega
  have h2n : 2 ≤ 2 ^ n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [pow_succ]
    have h1 := Nat.one_le_two_pow (n := m)
    omega
  have hpos : 0 < 2 ^ n - 1 := by omega
  have hle := Nat.le_of_dvd hpos hpq
  rw [hn]
  omega

private theorem false_of_two_trivial_planes
    (hℓ : 3 ≤ ℓ) (hn : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1)
    {t : Fin ℓ → Fˣ} (htp : ∀ i, t i ^ p = 1)
    {K : Subgroup ↥(StatedSp ℓ F)}
    (hKdef : K = stdLayer (diagSp F ℓ t))
    (hpl : ∀ k ∈ K, ∀ i, spEnd k (Pi.single (Sum.inl i) (1 : F)) ∈ stdPlane F ℓ i ∧
      spEnd k (Pi.single (Sum.inr i) (1 : F)) ∈ stdPlane F ℓ i)
    {i₀ : Fin ℓ} (hone : ∀ j, j ≠ i₀ → t j = 1) : False := by
  have hcard3 : 1 < (Finset.univ.erase i₀).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j₁, hj₁, j₂, hj₂, hjne⟩ := Finset.one_lt_card.mp hcard3
  have hj₁' : j₁ ≠ i₀ := (Finset.mem_erase.mp hj₁).1
  have hj₂' : j₂ ≠ i₀ := (Finset.mem_erase.mp hj₂).1
  obtain ⟨X, hXp, hXc, g, hgX, hge⟩ :=
    exists_perfect_le_centralizer_diagSp (F := F) (ℓ := ℓ)
      (four_le_card_of_prime_dvd hp hp2 hn hpq) hjne
  have hXc' : X ≤ Subgroup.centralizer ({diagSp F ℓ t} : Set ↥(StatedSp ℓ F)) :=
    hXc t (hone j₁ hj₁') (hone j₂ hj₂')
  have htp' : t ^ p = 1 := by funext i; simpa using htp i
  have hxp : (diagSp F ℓ t) ^ p = 1 := by rw [← map_pow, htp', map_one]
  have hXK : X ≤ K := by
    simpa [hKdef] using le_stdLayer_of_perfect (ℓ := ℓ) (p := p) (by omega) hp hp2
      (diagSp F ℓ t) hxp hXc' hXp
  have hmem : spEnd g (Pi.single (Sum.inl j₁) (1 : F)) ∈ stdPlane F ℓ j₁ :=
    (hpl g (hXK hgX) j₁).1
  rw [hge] at hmem
  have hnot : (Pi.single (Sum.inl j₂) (1 : F) : Fin ℓ ⊕ Fin ℓ → F) ∉ stdPlane F ℓ j₁ := by
    rw [mem_stdPlane_iff]
    intro h
    have h0 : (Pi.single (Sum.inl j₂) (1 : F) : Fin ℓ ⊕ Fin ℓ → F) (Sum.inl j₂) = 0 :=
      h (Sum.inl j₂) (by
        rw [mem_coords]
        push Not
        exact ⟨fun h => hjne (Sum.inl_injective h).symm, Sum.inl_ne_inr⟩)
    rw [Pi.single_eq_same] at h0
    exact one_ne_zero h0
  exact hnot hmem


private theorem false_of_preserves_planes
    (hℓ : 3 ≤ ℓ) (hn : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1)
    {V K : Subgroup ↥(StatedSp ℓ F)}
    (hV : V = CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p)
    {t : Fin ℓ → Fˣ} (htp : ∀ i, t i ^ p = 1)
    (hKp : ⁅K, K⁆ = K)
    (hKc : K ≤ Subgroup.centralizer ({diagSp F ℓ t} : Set ↥(StatedSp ℓ F)))
    (hcent : V ⊓ Subgroup.centralizer (K : Set ↥(StatedSp ℓ F)) =
      Subgroup.zpowers (diagSp F ℓ t))
    (hpl : ∀ k ∈ K, ∀ i, spEnd k (Pi.single (Sum.inl i) (1 : F)) ∈ stdPlane F ℓ i ∧
      spEnd k (Pi.single (Sum.inr i) (1 : F)) ∈ stdPlane F ℓ i)
    (hKdef : K = stdLayer (diagSp F ℓ t))
    (hd1 : diagSp F ℓ t ≠ 1) : False := by
  have hsingle : ∀ i₁ i₂ : Fin ℓ, i₁ ≠ i₂ → t i₁ ≠ 1 → t i₂ ≠ 1 → False :=
    fun i₁ i₂ => not_two_ne_one_of_preserves_planes hp hn hpq hV htp hKp hKc hpl hcent
  have htex : ∃ i, t i ≠ 1 := by
    by_contra h
    push Not at h
    apply hd1
    have ht1 : t = 1 := by
      funext i
      simpa using h i
    rw [ht1, map_one]
  obtain ⟨i₀, hi₀⟩ := htex
  have hone : ∀ j, j ≠ i₀ → t j = 1 := by
    intro j hj
    by_contra htj
    exact hsingle j i₀ hj htj hi₀
  exact false_of_two_trivial_planes hℓ hn hp hp2 hpq htp hKdef hpl hone

private theorem commonFixed_ne_bot_ne_top
    (hℓ : 1 ≤ ℓ) (hn : Nat.card F = 2 ^ n)
    {T : Subgroup ↥(StatedSp ℓ F)} (hT1 : T ≠ ⊥) (hT2 : IsPGroup 2 T) :
    commonFixed T ≠ ⊥ ∧ commonFixed T ≠ ⊤ := by
  constructor
  · obtain ⟨v, hv0, hv⟩ := exists_ne_zero_mem_commonFixed (ℓ := ℓ) hT2 (by omega) hn
    have hvW : v ∈ commonFixed T := hv
    intro hbot
    rw [hbot] at hvW
    exact hv0 (by simpa using hvW)
  · obtain ⟨tT, htT⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT1
    have hsp : spEnd (tT : ↥(StatedSp ℓ F)) ≠ 1 := by
      intro h
      apply htT
      apply Subtype.ext
      show (tT : ↥(StatedSp ℓ F)) = 1
      have hlin : spLin ℓ F (tT : ↥(StatedSp ℓ F)) = spLin ℓ F 1 := by
        rw [map_one]
        exact Units.ext h
      exact spLin_injective hlin
    obtain ⟨v, hv⟩ : ∃ v, spEnd (tT : ↥(StatedSp ℓ F)) v ≠ v := by
      by_contra h
      push Not at h
      exact hsp (LinearMap.ext h)
    intro htop
    have hvW : v ∈ commonFixed T := by rw [htop]; exact Submodule.mem_top
    exact hv (mem_commonFixed.1 hvW tT tT.2)

theorem stdVanishes_symplecticQTorus (hℓ : 3 ≤ ℓ) (hn : Nat.card F = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1)
    {d : ↥(StatedSp ℓ F)}
    (hd : IsStdElt p (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p) d) :
    StdVanishes (CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p) d := by
  classical
  set V := CFSG.LocalAnalysis.GLTheoremA.Y10F.symplecticQTorus (F := F) (ℓ := ℓ) p with hV
  set K := stdLayer d with hK
  have hd' : IsStdElt p V d := hd
  obtain ⟨t, htp, hdt⟩ :=
    (CFSG.LocalAnalysis.GLTheoremA.Y10F.mem_symplecticQTorus (F := F) (ℓ := ℓ)).1 hd'.1
  have hKp : ⁅K, K⁆ = K :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hd'.2.2.2.1.2.2.1)
  have hKc : K ≤ Subgroup.centralizer ({diagSp F ℓ t} : Set ↥(StatedSp ℓ F)) := by
    simpa [hK, hdt] using hd'.2.2.2.1.1
  have hcent : V ⊓ Subgroup.centralizer (K : Set ↥(StatedSp ℓ F)) =
      Subgroup.zpowers (diagSp F ℓ t) := by
    simpa [hK, hdt] using hd'.2.2.2.2
  rintro ⟨T, hT1, hT2, hN⟩
  set W := commonFixed T with hW
  obtain ⟨hW0, hWtop⟩ := commonFixed_ne_bot_ne_top (T := T) (by omega) hn hT1 hT2
  obtain ⟨hinner, hVn⟩ := sup_le_iff.mp hN
  have hWV : ∀ g ∈ V, ∀ w ∈ W, spEnd g w ∈ W :=
    fun g hg w hw => commonFixed_normalizer_maps (T := T) (hVn hg) hw
  have hWK : ∀ nn ∈ Subgroup.normalizer (V : Set ↥(StatedSp ℓ F)), ∀ k ∈ K,
      ∀ w ∈ W, spEnd (nn * k * nn⁻¹) w ∈ W := by
    intro nn hnn k hk w hw
    refine commonFixed_normalizer_maps (T := T) (hinner ?_) hw
    have hmap : (MulAut.conj nn).toMonoidHom k ∈ K.map (MulAut.conj nn).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hk
    have hconj : (MulAut.conj nn).toMonoidHom k = nn * k * nn⁻¹ :=
      MulAut.conj_apply nn k
    rw [innerClosure, closureIn, ← hK]
    refine Subgroup.mem_iSup_of_mem nn (Subgroup.mem_iSup_of_mem hnn ?_)
    rwa [hconj] at hmap
  rcases preserves_lines_or_planes (F := F) (ℓ := ℓ) hp hp2 hn hpq
      (K := K) (W := W) hW0 hWtop hWV hWK with hlines | hplanes
  · exact not_commutative_of_isComponentOf hd'.2.2.2.1
      (mul_comm_of_forall_preserves_lines hlines)
  · have hKdef : K = stdLayer (diagSp F ℓ t) := by rw [hK, hdt]
    refine false_of_preserves_planes hℓ hn hp hp2 hpq hV htp hKp hKc hcent hplanes hKdef ?_
    intro hzero
    exact hd'.2.1 (hdt.trans hzero)

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
