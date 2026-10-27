module

public import CFSG.Quasithin.Background.OddCoprimeFixV
public import CFSG.CGT.PushingUpLit.CGT6.EmbAmb
public import CFSG.CGT.PushingUpLit.CGT6.EmbShort
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit CFSG.Quasithin
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open CFSG.Assembly (KProper InCatalog)
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem noTwoQuotient_map_hom (f : G →* G') {Y : Subgroup G} (hY : SubTwo.NoTwoQuotient Y) :
    SubTwo.NoTwoQuotient (Y.map f) := by
  intro N hNY hnorm h2
  have hN : (Y ⊓ N.comap f) = Y := by
    apply hY
    · exact inf_le_left
    · intro y hy
      rw [Subgroup.mem_normalizer_iff]
      have hfy : f y ∈ Subgroup.normalizer (N : Set G') := hnorm ⟨y, hy, rfl⟩
      intro x
      simp only [Subgroup.mem_inf, Subgroup.mem_comap, map_mul, map_inv]
      constructor
      · rintro ⟨hxY, hxN⟩
        exact ⟨Y.mul_mem (Y.mul_mem hy hxY) (Y.inv_mem hy),
          (Subgroup.mem_normalizer_iff.mp hfy (f x)).mp hxN⟩
      · rintro ⟨hxY, hxN⟩
        refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hfy (f x)).mpr hxN⟩
        have := Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hxY) hy
        simpa [mul_assoc] using this
    · intro y hy
      obtain ⟨k, hk⟩ := h2 (f y) ⟨y, hy, rfl⟩
      exact ⟨k, Subgroup.mem_inf.mpr ⟨Y.pow_mem hy _, by rw [Subgroup.mem_comap, map_pow]; exact hk⟩⟩
  apply le_antisymm hNY
  rintro _ ⟨y, hy, rfl⟩
  have : y ∈ Y ⊓ N.comap f := by rw [hN]; exact hy
  exact (Subgroup.mem_inf.mp this).2

theorem map_mem_normalizer_map (f : G →* G') {S : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) : f g ∈ Subgroup.normalizer (S.map f : Set G') := by
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ {g : G}, g ∈ Subgroup.normalizer (S : Set G) →
      ∀ t ∈ S.map f, f g * t * (f g)⁻¹ ∈ S.map f := by
    intro g hg t ht
    obtain ⟨s, hs, rfl⟩ := ht
    exact ⟨g * s * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg s).mp hs, by simp⟩
  intro t
  refine ⟨key hg t, fun h => ?_⟩
  have h' := key (Subgroup.inv_mem _ hg) _ h
  simpa [mul_assoc] using h'

end Transport

section OddCoprime

variable {V : Type} [CommGroup V]

theorem commV_inf_fixV_eq_bot_of_odd (hV : ∀ v : V, v ^ 2 = 1) (Ŷ : Subgroup (MulAut V))
    [Finite Ŷ] (hodd : Odd (Nat.card Ŷ)) : commV Ŷ ⊓ fixV Ŷ = ⊥ :=
  CFSG.Quasithin.commV_inf_fixV_eq_bot_of_odd_card hV Ŷ hodd

end OddCoprime

section Commute

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem commutator_eq_bot_of_subnormal_sup {Y T H : Subgroup Γ} (hNo : SubTwo.NoTwoQuotient Y)
    (hT2 : IsPGroup 2 T) (hYT : Y ≤ Subgroup.normalizer (T : Set Γ)) (hYH : Y ≤ H) (hTH : T ≤ H)
    (hs : (Y.subgroupOf H).IsSubnormal) (hO : ⁅oTwoIn Y, Y⁆ = ⊥)
    (hcase : ⁅Y, Y⁆ = Y ∨ Nat.card ↥Y = 3) : ⁅T, Y⁆ = ⊥ := by
  have hTY : T ≤ Subgroup.normalizer (Y : Set Γ) :=
    le_normalizer_of_isSubnormal_of_le hNo hT2 hYT hYH hTH hs
  have hle : ⁅T, Y⁆ ≤ oTwoIn Y := commutator_le_oTwoIn_of_normalizes hT2 hTY hYT
  rcases hcase with hperf | h3
  · have h1 : ⁅⁅T, Y⁆, Y⁆ = ⊥ := by
      rw [eq_bot_iff, ← hO]
      exact Subgroup.commutator_mono hle le_rfl
    have h2 : ⁅⁅Y, T⁆, Y⁆ = ⊥ := by rw [Subgroup.commutator_comm Y T]; exact h1
    have h3 : ⁅⁅Y, Y⁆, T⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
    rw [hperf] at h3
    rw [Subgroup.commutator_comm]
    exact h3
  · rw [eq_bot_iff]
    intro x hx
    have hxY : x ∈ Y := Subgroup.le_normalizer_iff_commutator_le_right.mp hTY hx
    have hxT : x ∈ T := Subgroup.le_normalizer_iff_commutator_le_left.mp hYT hx
    obtain ⟨k, hk⟩ := hT2 ⟨x, hxT⟩
    have hx2 : x ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hx3 : x ^ 3 = 1 := by
      have : (⟨x, hxY⟩ : ↥Y) ^ Nat.card ↥Y = 1 := pow_card_eq_one'
      rw [h3] at this
      have := congrArg Subtype.val this
      simpa using this
    have hg : Nat.gcd (2 ^ k) 3 = 1 := by
      apply Nat.Coprime.pow_left
      norm_num
    have : x ^ Nat.gcd (2 ^ k) 3 = 1 := pow_gcd_eq_one.mpr ⟨hx2, hx3⟩
    rw [hg, pow_one] at this
    exact this

end Commute

section Perfect

variable {G : Type} [Group G] [Finite G]

theorem commutator_eq_top_of_quotient {L : Type} [Group L] (hres : oResidualTwo L = ⊤)
    (hq : commutator (L ⧸ pCore 2 L) = ⊤) : commutator L = ⊤ := by
  have hsup : commutator L ⊔ pCore 2 L = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 : QuotientGroup.mk' (pCore 2 L) x ∈ (commutator L).map (QuotientGroup.mk' (pCore 2 L)) := by
      have : (commutator L).map (QuotientGroup.mk' (pCore 2 L)) = commutator (L ⧸ pCore 2 L) := by
        unfold commutator
        rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
      rw [this, hq]
      exact Subgroup.mem_top _
    obtain ⟨d, hd, hdx⟩ := h1
    have hx : x = d * (d⁻¹ * x) := by group
    rw [hx]
    refine Subgroup.mul_mem_sup hd ?_
    rw [← QuotientGroup.eq_one_iff]
    simp [QuotientGroup.mk'_apply] at hdx ⊢
    rw [hdx]
    simp
  have h2 : IsPGroup 2 (L ⧸ commutator L) := by
    have hsurj : Function.Surjective ((QuotientGroup.mk' (commutator L)).comp (pCore 2 L).subtype) := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (commutator L) y
      have hx : x ∈ commutator L ⊔ pCore 2 L := by rw [hsup]; exact Subgroup.mem_top _
      obtain ⟨d, hd, p, hp, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      refine ⟨⟨p, hp⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using (inferInstance : (commutator L).Normal).conj_mem' d hd p
    exact (pCore_isPGroup (p := 2) (G := L)).of_surjective _ hsurj
  have h3 : oResidualTwo L ≤ commutator L := sInf_le ⟨inferInstance, h2⟩
  rw [hres] at h3
  exact top_le_iff.mp h3

theorem commutator_self_eq_of_isShortGroup {Y : Subgroup G} (hY : IsShortGroup ↥Y)
    (hq : IsQuasisimple (↥Y ⧸ pCore 2 ↥Y)) : ⁅Y, Y⁆ = Y := by
  have h1 : commutator ↥Y = ⊤ :=
    commutator_eq_top_of_quotient hY.residual_eq (Group.isPerfect_def.mp hq.1)
  have h2 : (commutator ↥Y).map Y.subtype = ⁅Y, Y⁆ := by
    unfold commutator
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Y.range_subtype]
  rw [← h2, h1, ← MonoidHom.range_eq_map, Y.range_subtype]

end Perfect

section Prime

theorem prime_case_card {L : Type} [Group L] [Finite L] (hL : InClassX L)
    (hp : (Nat.card (L ⧸ pCore 2 L)).Prime) :
    Nat.card (L ⧸ pCore 2 L) = 3 ∧ Nat.card ↥(shortU L) = 4 * Nat.card ↥(shortC L) := by
  rcases hL.2 with ⟨n, hn, φ, ψ, hsum, hsurj, hker, -⟩ | ⟨n, hn, φ, ψ, hsurj, hker, -⟩
  · have hcard : Nat.card (L ⧸ pCore 2 L) = (2 * n + 1).factorial / 2 := by
      have : Nontrivial (Fin (2 * n + 1)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
      rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have hn1 : n = 1 := by
      by_contra hne
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      have hfac : (2 * (k + 2) + 1).factorial / 2 =
          (k + 2) * ((2 * k + 5) * (2 * k + 3).factorial) := by
        have e : 2 * (k + 2) + 1 = (2 * k + 3) + 1 + 1 := by ring
        rw [e, Nat.factorial_succ, Nat.factorial_succ]
        have : (2 * k + 3 + 1 + 1) * ((2 * k + 3 + 1) * (2 * k + 3).factorial) =
            2 * ((k + 2) * ((2 * k + 5) * (2 * k + 3).factorial)) := by ring
        rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
      rw [hcard, hfac] at hp
      have h1 : (2 * k + 5) * (2 * k + 3).factorial ≠ 1 := by
        have := Nat.factorial_pos (2 * k + 3)
        intro h
        have h2 : 2 * k + 5 ∣ 1 := h ▸ dvd_mul_right _ _
        have := Nat.le_of_dvd one_pos h2
        omega
      exact Nat.not_prime_mul (by omega) h1 hp
    subst hn1
    refine ⟨by rw [hcard]; decide, ?_⟩
    have hrange : Nat.card ψ.range = 4 := by
      have e : ψ.range ≃ {v : Fin (2 * 1 + 1) → ZMod 2 // ∑ i, v i = 0} :=
        { toFun := fun x => ⟨Multiplicative.toAdd (x : Multiplicative (Fin (2 * 1 + 1) → ZMod 2)), by
            obtain ⟨_, ⟨u, rfl⟩⟩ := x
            exact hsum u⟩
          invFun := fun v => ⟨Multiplicative.ofAdd v.1, by
            obtain ⟨u, hu⟩ := hsurj v.1 v.2
            exact ⟨u, hu⟩⟩
          left_inv := fun x => by simp
          right_inv := fun v => by simp }
      rw [Nat.card_congr e, Nat.card_eq_fintype_card]
      decide
    have hle : shortC L ≤ shortU L := inf_le_left
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hrange, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
    exact h1
  · exfalso
    have : Finite (GaloisField 2 n) := inferInstance
    have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
    have hcard : Nat.card (L ⧸ pCore 2 L) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr φ.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    rw [hcard] at hp
    have h1 : 2 ^ n ≠ 1 := by
      have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
      omega
    have h2 : (2 ^ n) ^ 2 - 1 ≠ 1 := by
      have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
      have : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    exact Nat.not_prime_mul h1 h2 hp

end Prime

section Ambient

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} [V.Normal]

omit [Finite G] in
theorem mem_normalizer_of_conj_mem {H : Subgroup G} {g : G} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h' : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have := h' _ hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem map_sup_centralizer_ambRho (P : Subgroup G) :
    (P ⊔ Subgroup.centralizer (V : Set G)).map (ambRho V) = P.map (ambRho V) := by
  rw [Subgroup.map_sup, ← ker_ambRho V]
  have : (ambRho V).ker.map (ambRho V) = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl
  rw [this, sup_bot_eq]

omit [Finite G] in
theorem le_ker_ambRho (hV : IsElemAbelian 2 V) : V ≤ (ambRho V).ker := by
  rw [ker_ambRho V]
  exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.1

theorem oTwoIn_map_le {Y : Subgroup G} (hY : InClassX ↥Y) (hU : ⁅V, Y⁆ = ⁅oTwoIn Y, Y⁆) :
    oTwoIn (Y.map (ambRho V)) ≤ (oTwoIn Y).map (ambRho V) := by
  set ρ := ambRho V with hρ
  set Ô := oTwoIn (Y.map ρ) with hÔ
  intro o hoO
  have hoŶ : o ∈ Y.map ρ := SixThree.oTwoIn_le _ hoO
  obtain ⟨y, hy, rfl⟩ := hoŶ
  have hK : Y ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoIn Y := inf_centralizer_le_oTwoIn hY hU
  set Õ : Subgroup G := Y ⊓ Ô.comap ρ with hÕ
  have hÕ2 : IsPGroup 2 Õ := by
    intro x
    have hxÔ : ρ (x : G) ∈ Ô := (Subgroup.mem_inf.mp x.2).2
    have hxY : (x : G) ∈ Y := (Subgroup.mem_inf.mp x.2).1
    obtain ⟨k, hk⟩ := SixThree.isPGroup_oTwoIn (Y.map ρ) ⟨ρ x, hxÔ⟩
    have hk' : ρ ((x : G) ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have hker : (x : G) ^ 2 ^ k ∈ oTwoIn Y := by
      apply hK
      refine Subgroup.mem_inf.mpr ⟨Y.pow_mem hxY _, ?_⟩
      rw [← ker_ambRho V]
      exact hk'
    obtain ⟨j, hj⟩ := SixThree.isPGroup_oTwoIn Y ⟨_, hker⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have := congrArg Subtype.val hj
    simpa [pow_add, pow_mul] using this
  have hÕY : Õ ≤ Y := inf_le_left
  have hn : Y ≤ Subgroup.normalizer (Õ : Set G) := by
    intro y' hy'
    have key : ∀ y'' ∈ Y, ∀ x ∈ Õ, y'' * x * y''⁻¹ ∈ Õ := by
      intro y'' hy'' x hx
      obtain ⟨hxY, hxÔ⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨Y.mul_mem (Y.mul_mem hy'' hxY) (Y.inv_mem hy''), ?_⟩
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact conj_mem_oTwoIn (Subgroup.le_normalizer (H := Y.map ρ) ⟨y'', hy'', rfl⟩) hxÔ
    exact mem_normalizer_of_conj_mem (key y' hy') (fun x hx => by
      simpa using key y'⁻¹ (Y.inv_mem hy') x hx)
  have hÕO : Õ ≤ oTwoIn Y := SixThree.le_oTwoIn_of_isPGroup hÕY hÕ2 hn
  exact ⟨y, hÕO (Subgroup.mem_inf.mpr ⟨hy, hoO⟩), rfl⟩

omit [Finite G] in
theorem map_oTwoIn_central {Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hU : ⁅V, Y⁆ = ⁅oTwoIn Y, Y⁆) :
    ⁅(oTwoIn Y).map (ambRho V), Y.map (ambRho V)⁆ = ⊥ := by
  rw [← Subgroup.map_commutator, ← hU, Subgroup.map_eq_bot_iff]
  exact (Subgroup.commutator_le_left V Y).trans (le_ker_ambRho hV)

theorem card_autOn_eq_three {Y : Subgroup G} (hV : IsElemAbelian 2 V) (hY : InClassX ↥Y)
    (hp : (Nat.card (↥Y ⧸ pCore 2 ↥Y)).Prime) (hU : ⁅V, Y⁆ = ⁅oTwoIn Y, Y⁆) :
    Nat.card ↥(autOn Y V) = 3 := by
  classical
  set ρ := ambRho V with hρ
  rw [← map_ambRho V]
  obtain ⟨hq3, -⟩ := prime_case_card hY hp
  set Ŷ := Y.map ρ with hŶ
  set Ō := (oTwoIn Y).map ρ with hŌ
  have hK : Y ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoIn Y := inf_centralizer_le_oTwoIn hY hU
  have hŌ2 : IsPGroup 2 Ō := isPGroup_map_two (SixThree.isPGroup_oTwoIn Y) ρ
  have hcent : ∀ ō ∈ Ō, ∀ ŷ ∈ Ŷ, ŷ * ō = ō * ŷ := by
    intro ō hō ŷ hŷ
    have h1 : ⁅ō, ŷ⁆ ∈ ⁅Ō, Ŷ⁆ := Subgroup.commutator_mem_commutator hō hŷ
    rw [map_oTwoIn_central hV hU] at h1
    have h2 : ⁅ō, ŷ⁆ = 1 := Subgroup.mem_bot.mp h1
    exact ((commutatorElement_eq_one_iff_mul_comm).mp h2).symm
  have hcardY : Nat.card ↥Y = 3 * Nat.card ↥(pCore 2 ↥Y) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥Y)
    rw [hq3] at this
    exact this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype ↥Y := Fintype.ofFinite _
  obtain ⟨g', hg'⟩ := exists_prime_orderOf_dvd_card (G := ↥Y) 3
    (by rw [← Nat.card_eq_fintype_card, hcardY]; exact dvd_mul_right _ _)
  have hg'not : g' ∉ pCore 2 ↥Y := by
    intro h
    obtain ⟨k, hk⟩ := pCore_isPGroup (p := 2) (G := ↥Y) ⟨g', h⟩
    have h1 : g' ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : orderOf g' ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    rw [hg'] at h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
    omega
  set g : G := (g' : G) with hg
  have hgY : g ∈ Y := g'.2
  have hg3 : g ^ 3 = 1 := by
    have : g' ^ 3 = 1 := by rw [← hg']; exact pow_orderOf_eq_one g'
    simpa using congrArg Subtype.val this
  have hdecomp : ∀ y ∈ Y, ∃ m : ℤ, (g ^ m)⁻¹ * y ∈ oTwoIn Y := by
    intro y hy
    have hne : (QuotientGroup.mk g' : ↥Y ⧸ pCore 2 ↥Y) ≠ 1 := fun h =>
      hg'not ((QuotientGroup.eq_one_iff g').mp h)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_prime_card hq3 hne : (QuotientGroup.mk ⟨y, hy⟩ : ↥Y ⧸ pCore 2 ↥Y) ∈
        Subgroup.zpowers (QuotientGroup.mk g'))
    refine ⟨m, ?_⟩
    have h1 : ((g' ^ m)⁻¹ * ⟨y, hy⟩ : ↥Y) ∈ pCore 2 ↥Y := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_zpow, hm, inv_mul_cancel]
    exact ⟨_, h1, by simp [hg]⟩
  set t : MulAut ↥V := ρ g with ht
  have htŶ : t ∈ Ŷ := ⟨g, hgY, rfl⟩
  have hŶdecomp : ∀ ŷ ∈ Ŷ, ∃ (m : ℤ) (ō : MulAut ↥V), ō ∈ Ō ∧ ŷ = t ^ m * ō := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨m, hm⟩ := hdecomp y hy
    refine ⟨m, ρ ((g ^ m)⁻¹ * y), ⟨_, hm, rfl⟩, ?_⟩
    rw [map_mul, map_inv, map_zpow, ← ht, mul_inv_cancel_left]
  have htcomm : ∀ ŷ ∈ Ŷ, t * ŷ = ŷ * t := by
    intro ŷ hŷ
    obtain ⟨m, ō, hō, rfl⟩ := hŶdecomp ŷ hŷ
    have h1 : Commute t ō := hcent ō hō t htŶ
    have h2 : Commute t (t ^ m) := (Commute.refl t).zpow_right m
    exact (h2.mul_right h1)
  have hNo : SubTwo.NoTwoQuotient Ŷ :=
    noTwoQuotient_map_hom ρ (SubTwo.noTwoQuotient_of_oResidualTwo hY.1.residual_eq)
  have hzp : Subgroup.zpowers t = Ŷ := by
    apply hNo
    · exact Subgroup.zpowers_le.mpr htŶ
    · intro ŷ hŷ
      have hc : ∀ x ∈ Subgroup.zpowers t, ŷ * x * ŷ⁻¹ ∈ Subgroup.zpowers t := by
        intro x hx
        have : Commute ŷ x := by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
          exact (show Commute ŷ t from (htcomm ŷ hŷ).symm).zpow_right k
        rw [this.eq]; simpa using hx
      refine mem_normalizer_of_conj_mem hc (fun x hx => ?_)
      have hŷ' : ŷ⁻¹ ∈ Ŷ := Ŷ.inv_mem hŷ
      have : Commute ŷ⁻¹ x := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact (show Commute ŷ⁻¹ t from (htcomm ŷ⁻¹ hŷ').symm).zpow_right k
      rw [this.eq]; simpa using hx
    · intro ŷ hŷ
      obtain ⟨m, ō, hō, rfl⟩ := hŶdecomp ŷ hŷ
      obtain ⟨k, hk⟩ := hŌ2 ⟨ō, hō⟩
      have hk' : ō ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      refine ⟨k, ?_⟩
      have hcm : Commute (t ^ m) ō := (show Commute t ō from hcent ō hō t htŶ).zpow_left m
      rw [hcm.mul_pow, hk', mul_one, ← zpow_natCast, ← zpow_mul]
      exact Subgroup.zpow_mem_zpowers t _
  have htne : t ≠ 1 := by
    intro h1
    apply hg'not
    have hgK : g ∈ Y ⊓ Subgroup.centralizer (V : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hgY, ?_⟩
      rw [← ker_ambRho V]
      exact h1
    obtain ⟨g'', hg''p, hg''⟩ := hK hgK
    have : g'' = g' := Subtype.ext hg''
    rw [← this]
    exact hg''p
  have hord : orderOf t = 3 := orderOf_eq_prime (by rw [ht, ← map_pow, hg3, map_one]) htne
  rw [← hzp, Nat.card_zpowers, hord]

theorem card_commOn_eq_four {Y : Subgroup G} (hV : IsElemAbelian 2 V) (hY : InClassX ↥Y)
    (hp : (Nat.card (↥Y ⧸ pCore 2 ↥Y)).Prime) (hU : ⁅V, Y⁆ = ⁅oTwoIn Y, Y⁆) :
    Nat.card ↥(commOn hV Y) = 4 := by
  classical
  have hY3 := card_autOn_eq_three hV hY hp hU
  have hodd : Odd (Nat.card ↥(autOn Y V)) := by rw [hY3]; exact ⟨1, rfl⟩
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV.2 v v.2)
  have hbot : commOn hV Y ⊓ fixOn hV Y = ⊥ :=
    @commV_inf_fixV_eq_bot_of_odd ↥V (commGroupOfElemAbelian hV) hV2 (autOn Y V) _ hodd
  have hYN : Y ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.normalizer_eq_top V]; exact le_top
  rw [commOn_eq hV hYN, fixOn_eq hV hYN] at hbot
  have hVc : ⁅Y, V⁆ ≤ V := Subgroup.commutator_le_right Y V
  have hbot' : (⁅Y, V⁆ : Subgroup G) ⊓ Subgroup.centralizer (Y : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxV : x ∈ V := hVc hx.1
    have : (⟨x, hxV⟩ : ↥V) ∈ (⁅Y, V⁆ : Subgroup G).subgroupOf V ⊓
        (Subgroup.centralizer (Y : Set G)).subgroupOf V := Subgroup.mem_inf.mpr ⟨hx.1, hx.2⟩
    rw [hbot] at this
    have h1 : (⟨x, hxV⟩ : ↥V) = 1 := Subgroup.mem_bot.mp this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  have hC : SixThree.shortCIn Y = ⊥ := by
    rw [eq_bot_iff, ← hbot']
    refine le_inf ?_ (SixThree.shortCIn_le_centralizer Y)
    rw [Subgroup.commutator_comm, hU]
    exact SixThree.shortCIn_le_U Y
  have hC' : Nat.card ↥(shortC ↥Y) = 1 := by
    have : shortC ↥Y = ⊥ := by
      have h0 : (shortC ↥Y).map Y.subtype = ⊥ := hC
      rw [Subgroup.map_eq_bot_iff] at h0
      rw [eq_bot_iff]
      intro x hx
      have : Y.subtype x = 1 := by
        have := h0 hx
        simpa using this
      exact Subgroup.mem_bot.mpr (Subtype.ext this)
    rw [this]
    exact Subgroup.card_bot
  obtain ⟨-, hU4⟩ := prime_case_card hY hp
  rw [hC', mul_one] at hU4
  have hmap : Nat.card ↥(⁅oTwoIn Y, Y⁆ : Subgroup G) = Nat.card ↥(shortU ↥Y) := by
    rw [← map_shortU]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ Y.subtype Y.subtype_injective).toEquiv.symm
  rw [commOn_eq hV hYN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVc).toEquiv,
    Subgroup.commutator_comm, hU, hmap, hU4]

omit [Finite G] in
theorem mem_normalizer_of_map_normalizer {G' : Type*} [Group G'] (f : G →* G') {S : Subgroup G}
    (hS : f.ker ≤ S) {g : G} (hg : f g ∈ Subgroup.normalizer (S.map f : Set G')) :
    g ∈ Subgroup.normalizer (S : Set G) := by
  have key : ∀ g, f g ∈ Subgroup.normalizer (S.map f : Set G') → ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
    intro g hg s hs
    have h1 : f (g * s * g⁻¹) ∈ S.map f := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hg (f s)).mp ⟨s, hs, rfl⟩
    obtain ⟨w, hw, hww⟩ := h1
    have : g * s * g⁻¹ = w * (w⁻¹ * (g * s * g⁻¹)) := by group
    rw [this]
    refine S.mul_mem hw (hS ?_)
    rw [MonoidHom.mem_ker, map_mul, map_inv, hww, inv_mul_cancel]
  refine mem_normalizer_of_conj_mem (key g hg) (fun x hx => ?_)
  have hginv : f g⁻¹ ∈ Subgroup.normalizer (S.map f : Set G') := by
    rw [map_inv]; exact Subgroup.inv_mem _ hg
  simpa using key g⁻¹ hginv x hx

end Ambient

section Main

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} [V.Normal]

theorem emb_hyp_data (hK : KProper InCatalog G) {Y P : Subgroup G} (hV : IsElemAbelian 2 V)
    (hY : InClassX ↥Y) (hP2 : IsPGroup 2 P) (hPC : ¬ P ≤ Subgroup.centralizer (V : Set G))
    (hYN : Y ≤ Subgroup.normalizer
      ((P ⊔ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
    (hs : (Y.subgroupOf (Subgroup.normalizer
      ((P ⊔ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))).IsSubnormal)
    (hU : ⁅V, Y⁆ = ⁅oTwoIn Y, Y⁆) :
    KProper InCatalog ↥(autOn (⊤ : Subgroup G) V) ∧
    autOn P V ≤ autOn (⊤ : Subgroup G) V ∧ autOn P V ≠ ⊥ ∧ IsPGroup 2 ↥(autOn P V) ∧
    autOn Y V ≤ autOn (⊤ : Subgroup G) V ⊓ Subgroup.centralizer (autOn P V : Set (MulAut ↥V)) ∧
    ((autOn Y V).subgroupOf (autOn (⊤ : Subgroup G) V ⊓
      Subgroup.centralizer (autOn P V : Set (MulAut ↥V)))).IsSubnormal ∧
    (⁅autOn Y V, autOn Y V⁆ = autOn Y V ∨
      (Nat.card ↥(autOn Y V) = 3 ∧ Nat.card ↥(commOn hV Y) = 4)) := by
  classical
  set ρ := ambRho V with hρ
  set C := Subgroup.centralizer (V : Set G) with hC
  set H := Subgroup.normalizer ((P ⊔ C : Subgroup G) : Set G) with hH
  have hDich : ⁅Y.map ρ, Y.map ρ⁆ = Y.map ρ ∨
      (Nat.card ↥(Y.map ρ) = 3 ∧ Nat.card ↥(commOn hV Y) = 4) := by
    rcases hY.1.quotient_type with hq | hp
    · left
      rw [← Subgroup.map_commutator, commutator_self_eq_of_isShortGroup hY.1 hq]
    · right
      refine ⟨?_, card_commOn_eq_four hV hY hp hU⟩
      rw [map_ambRho V]
      exact card_autOn_eq_three hV hY hp hU
  have hT : (P ⊔ C).map ρ = P.map ρ := map_sup_centralizer_ambRho P
  have hPH : P ≤ H := le_sup_left.trans Subgroup.le_normalizer
  have hYH : Y ≤ H := hYN
  have hYT : Y.map ρ ≤ Subgroup.normalizer (P.map ρ : Set (MulAut ↥V)) := by
    rintro _ ⟨y, hy, rfl⟩
    have := map_mem_normalizer_map ρ (S := P ⊔ C) (hYN hy)
    rwa [hT] at this
  have hsH : ((Y.map ρ).subgroupOf (H.map ρ)).IsSubnormal := by
    let f : ↥H →* ↥(H.map ρ) :=
      (ρ.comp H.subtype).codRestrict (H.map ρ) fun x => ⟨x, x.2, rfl⟩
    have hf : Function.Surjective f := by
      rintro ⟨_, ⟨x, hx, rfl⟩⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    have hmap : (Y.subgroupOf H).map f = (Y.map ρ).subgroupOf (H.map ρ) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · intro hz
        obtain ⟨y, hy, hyz⟩ := hz
        exact ⟨⟨y, hYH hy⟩, hy, Subtype.ext hyz⟩
    rw [← hmap]
    exact Subgroup.IsSubnormal.map hf hs
  have hNo : SubTwo.NoTwoQuotient (Y.map ρ) :=
    noTwoQuotient_map_hom ρ (SubTwo.noTwoQuotient_of_oResidualTwo hY.1.residual_eq)
  have hO : ⁅oTwoIn (Y.map ρ), Y.map ρ⁆ = ⊥ := by
    rw [eq_bot_iff, ← map_oTwoIn_central hV hU]
    exact Subgroup.commutator_mono (oTwoIn_map_le hY hU) le_rfl
  have hcomm : ⁅P.map ρ, Y.map ρ⁆ = ⊥ := by
    refine commutator_eq_bot_of_subnormal_sup hNo (isPGroup_map_two hP2 ρ) hYT
      (Subgroup.map_mono hYH) (Subgroup.map_mono hPH) hsH hO ?_
    rcases hDich with h | ⟨h3, -⟩
    · exact Or.inl h
    · exact Or.inr h3
  have hYc : Y.map ρ ≤ Subgroup.centralizer (P.map ρ : Set (MulAut ↥V)) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact hcomm))
  have hĜ : P.map ρ ≤ (⊤ : Subgroup G).map ρ := Subgroup.map_mono le_top
  have hLH : (⊤ : Subgroup G).map ρ ⊓ Subgroup.centralizer (P.map ρ : Set (MulAut ↥V)) ≤
      H.map ρ := by
    rintro x ⟨hxG, hxc⟩
    obtain ⟨g, -, rfl⟩ := hxG
    refine ⟨g, ?_, rfl⟩
    have hgn : ρ g ∈ Subgroup.normalizer
        (((P ⊔ C).map ρ : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) := by
      rw [hT]
      exact Subgroup.centralizer_le_normalizer _ hxc
    exact mem_normalizer_of_map_normalizer ρ (by rw [hρ, ker_ambRho V]; exact le_sup_right) hgn
  have hKp : KProper InCatalog ↥(autOn (⊤ : Subgroup G) V) :=
    CFSG.ComponentClassification.CatalogueKProper.of_surjective hK (ambRhoHat V)
      (ambRhoHat_surjective V)
  have eP : autOn P V = P.map ρ := (map_ambRho V P).symm
  have eY : autOn Y V = Y.map ρ := (map_ambRho V Y).symm
  have eG : autOn (⊤ : Subgroup G) V = (⊤ : Subgroup G).map ρ := (map_ambRho V ⊤).symm
  refine ⟨hKp, ?_⟩
  rw [eP, eY, eG]
  refine ⟨hĜ, ?_, isPGroup_map_two hP2 ρ, le_inf (Subgroup.map_mono le_top) hYc,
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hLH hsH, hDich⟩
  intro h
  apply hPC
  intro p hp
  have : ρ p ∈ P.map ρ := ⟨p, hp, rfl⟩
  rw [h] at this
  rw [hC, ← ker_ambRho V]
  exact Subgroup.mem_bot.mp this

end Main

end CFSG.CGT.PushingUpLit.CGT6
