module

public import CFSG.CGT.Timmesfeld75.Sec6Seven
public import CFSG.CGT.Timmesfeld75.SLTransvectionComm
public import CFSG.CGT.Timmesfeld75.Sec7OneDihedral

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups Matrix commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem false_of_sq_mem {d e : G} {k : ℕ} (hT : IsElemAbelian 2 T) (hk3 : 3 ≤ k)
    (ho : orderOf (d * e) = 2 * k) (hsq : (d * e) ^ 2 ∈ T) : False := by
  have h1 : ((d * e) ^ 2) * ((d * e) ^ 2) = 1 := elemAbelian_mul_self hT hsq
  have h2 : (d * e) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]
    exact h1
  have h3 : orderOf (d * e) ∣ 4 := orderOf_dvd_of_pow_eq_one h2
  rw [ho] at h3
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem sq_mem_of_mem_normalizer {d e : G} (hd2 : d * d = 1) (he2 : e * e = 1)
    (hdN : d ∈ Subgroup.normalizer (T : Set G)) (heN : e ∈ Subgroup.normalizer (T : Set G))
    (h : d ∈ T ∨ e ∈ T) : (d * e) ^ 2 ∈ T := by
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  rcases h with hdT | heT
  · have h1 := conj_mem_of_mem_normalizer heN hdT
    rw [hei] at h1
    have e1 : (d * e) ^ 2 = d * (e * d * e) := by rw [pow_two]; simp only [mul_assoc]
    rw [e1]
    exact T.mul_mem hdT h1
  · have h1 := conj_mem_of_mem_normalizer hdN heT
    rw [hdi] at h1
    have e1 : (d * e) ^ 2 = (d * e * d) * e := by rw [pow_two]; simp only [mul_assoc]
    rw [e1]
    exact T.mul_mem h1 heT

theorem Sec6Ctx.mem_commSub_of_dihedral (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ n m)
    {d e : G} (hdD : d ∈ normD T) (hdT : d ∉ T) {j : ℕ} (hd2 : d * d = 1) (he2 : e * e = 1)
    (hr : (d * e) ^ (2 * j) = 1) (hzd : (d * e) ^ j * d ∈ classD T)
    (hzT : (d * e) ^ j ∈ T) : (d * e) ^ j ∈ commSub d T := by
  have hset := hc.sec65 h62 h63 hdD hdT
  have hdz : d * (d * e) ^ j = (d * e) ^ j * d := (dihedral_center_comm hd2 he2 hr).1
  have hmem : (d * e) ^ j * d ∈ {y | y ∈ classD T ∧ ∃ t ∈ T, y = d * t} :=
    ⟨hzd, (d * e) ^ j, hzT, hdz.symm⟩
  rw [hset.1, hset.2] at hmem
  obtain ⟨c, hc', hcz⟩ := hmem
  have : (d * e) ^ j = c := by
    have h := hdz.trans hcz
    exact mul_left_cancel h
  rw [this]
  exact hc'

theorem toAdd_phi_comm {H : Subgroup G} [(T.subgroupOf H).Normal]
    {ε : ↥H ⧸ T.subgroupOf H ≃* SL(n, GaloisField 2 m)}
    {φ : ↥T ≃* Multiplicative (Fin n → GaloisField 2 m)}
    (hcompat : ∀ (h : ↥H) (t : ↥T) (hmem : (h : G) * t * (h : G)⁻¹ ∈ T),
      φ ⟨(h : G) * t * (h : G)⁻¹, hmem⟩ =
        Multiplicative.ofAdd (((ε (QuotientGroup.mk h) : SL(n, GaloisField 2 m)) :
          Matrix (Fin n) (Fin n) (GaloisField 2 m)).mulVec (Multiplicative.toAdd (φ t))))
    {d : G} (hdH : d ∈ H) (hdN : d ∈ Subgroup.normalizer (T : Set G)) {t : G} (ht : t ∈ T)
    (hct : ⁅d, t⁆ ∈ T) :
    Multiplicative.toAdd (φ ⟨⁅d, t⁆, hct⟩) =
      ((ε (QuotientGroup.mk (⟨d, hdH⟩ : ↥H)) : SL(n, GaloisField 2 m)) :
        Matrix (Fin n) (Fin n) (GaloisField 2 m)) *ᵥ Multiplicative.toAdd (φ ⟨t, ht⟩) -
        Multiplicative.toAdd (φ ⟨t, ht⟩) := by
  have hm : d * t * d⁻¹ ∈ T := conj_mem_of_mem_normalizer hdN ht
  have e1 : (⟨⁅d, t⁆, hct⟩ : ↥T) = ⟨d * t * d⁻¹, hm⟩ * (⟨t, ht⟩ : ↥T)⁻¹ := by
    apply Subtype.ext
    simp [commutatorElement_def]
  rw [e1, map_mul, map_inv]
  have h := hcompat ⟨d, hdH⟩ ⟨t, ht⟩ hm
  rw [h]
  simp [sub_eq_add_neg]

theorem classD_conj_mul {x : G} (hx : x ∈ classD T) (g : G) : g * x * g⁻¹ ∈ classD T := by
  have := classD_conj hx g⁻¹
  rwa [inv_inv] at this

theorem Sec6Ctx.false_of_center_mem_T (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n m) (hA8 : ¬ (n = 4 ∧ m = 1))
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) {d e : G} (hd : d ∈ classD T)
    (he : e ∈ classD T) {j : ℕ} (hj3 : 3 ≤ j) (ho : orderOf (d * e) = 2 * j)
    (hzT : (d * e) ^ j ∈ T) : False := by
  have hTwc := hc.hy.pair.wc
  have hTab := hTwc.1
  have hd2 : d * d = 1 := mul_self_eq_one_of_mem_classD hTab hd
  have he2 : e * e = 1 := mul_self_eq_one_of_mem_classD hTab he
  have hr : (d * e) ^ (2 * j) = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
  have hz1 : (d * e) ^ j ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  obtain ⟨hdz, hez⟩ := dihedral_center_comm hd2 he2 hr
  have hdC : d ∈ Subgroup.centralizer ({(d * e) ^ j} : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hdz.symm
  have heC : e ∈ Subgroup.centralizer ({(d * e) ^ j} : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hez.symm
  have hdN := hTwc.centralizer_le_normalizer hzT hz1 hdC
  have heN := hTwc.centralizer_le_normalizer hzT hz1 heC
  by_cases hdeT : d ∈ T ∨ e ∈ T
  · exact false_of_sq_mem hTab hj3 ho (sq_mem_of_mem_normalizer hd2 he2 hdN heN hdeT)
  push Not at hdeT
  obtain ⟨hdT, heT⟩ := hdeT
  have hdD : d ∈ normD T := ⟨hd, hdN⟩
  have heD : e ∈ normD T := ⟨he, heN⟩
  obtain ⟨hzd', hze'⟩ := dihedral_center_mul_mem (S := classD T)
    (fun g x hx => classD_conj_mul hx g) hd2 he2 hr hd he
  have hzd := hc.mem_commSub_of_dihedral h62 h63 hdD hdT hd2 he2 hr hzd' hzT
  have hz2 : ((d * e) ^ j) * ((d * e) ^ j) = 1 := by rw [← pow_add, ← two_mul]; exact hr
  have hz' : (e * d) ^ j = (d * e) ^ j := by
    rw [← dihedral_inv hd2 he2, inv_pow]
    exact inv_eq_of_mul_eq_one_right hz2
  have hr' : (e * d) ^ (2 * j) = 1 := by
    rw [← dihedral_inv hd2 he2, inv_pow, hr, inv_one]
  have hze : (d * e) ^ j ∈ commSub e T := by
    have := hc.mem_commSub_of_dihedral h62 h63 heD heT he2 hd2 hr' (by rwa [hz']) (hz' ▸ hzT)
    rwa [hz'] at this
  obtain ⟨hN, ε, φ, hcompat, htr⟩ := hc.sec67_transv h1 h63 hA8 hnat
  have := hN
  obtain ⟨hdH, hud⟩ := htr d hdD hdT
  obtain ⟨heH, hue⟩ := htr e heD heT
  obtain ⟨td, htd, hztd⟩ := (mem_commSub_iff hTab (by rw [pow_two]; exact hd2) hdN).1 hzd
  obtain ⟨te, hte, hzte⟩ := (mem_commSub_iff hTab (by rw [pow_two]; exact he2) heN).1 hze
  have hctd : ⁅d, td⁆ ∈ T := comm_mem_of_mem_normalizer hdN htd
  have hcte : ⁅e, te⁆ ∈ T := comm_mem_of_mem_normalizer heN hte
  have hxd := toAdd_phi_comm hcompat hdH hdN htd hctd
  have hxe := toAdd_phi_comm hcompat heH heN hte hcte
  have hzd_eq : (⟨(d * e) ^ j, hzT⟩ : ↥T) = ⟨⁅d, td⁆, hctd⟩ := Subtype.ext hztd
  have hze_eq : (⟨(d * e) ^ j, hzT⟩ : ↥T) = ⟨⁅e, te⁆, hcte⟩ := Subtype.ext hzte
  rw [← hzd_eq] at hxd
  rw [← hze_eq] at hxe
  have hw : Multiplicative.toAdd (φ ⟨(d * e) ^ j, hzT⟩) ≠ 0 := by
    intro h0
    have h1' : φ ⟨(d * e) ^ j, hzT⟩ = 1 := by
      have : φ ⟨(d * e) ^ j, hzT⟩ = Multiplicative.ofAdd 0 := by
        rw [← h0]
        rfl
      simpa using this
    have h2' : (⟨(d * e) ^ j, hzT⟩ : ↥T) = 1 := φ.injective (h1'.trans φ.map_one.symm)
    exact hz1 (congrArg Subtype.val h2')
  have hcomm := IsTransvection.commute_of_common_image hud hue hw (by simpa using hxd.symm)
    (by simpa using hxe.symm)
  have hmk : (QuotientGroup.mk (⟨d, hdH⟩ : ↥(hSub T (normIn T₁ T))) *
      QuotientGroup.mk (⟨e, heH⟩ : ↥(hSub T (normIn T₁ T))) :
        ↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) =
      QuotientGroup.mk (⟨e, heH⟩ : ↥(hSub T (normIn T₁ T))) *
        QuotientGroup.mk (⟨d, hdH⟩ : ↥(hSub T (normIn T₁ T))) := by
    apply ε.injective
    rw [map_mul, map_mul]
    exact hcomm
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hmk
  have hmem := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hmk)
  have h5 : (e * d) ^ 2 ∈ T := by
    have e1 : ((d * e)⁻¹ * (e * d)) = (e * d) ^ 2 := by
      rw [dihedral_inv hd2 he2, pow_two]
    have e2 : (↑((⟨d, hdH⟩ * ⟨e, heH⟩ : ↥(hSub T (normIn T₁ T)))⁻¹ *
        (⟨e, heH⟩ * ⟨d, hdH⟩ : ↥(hSub T (normIn T₁ T)))) : G) = (d * e)⁻¹ * (e * d) := rfl
    rw [e2, e1] at hmem
    exact hmem
  have h6 : (d * e) ^ 2 ∈ T := by
    have e1 : (d * e) ^ 2 = ((e * d) ^ 2)⁻¹ := by
      rw [← dihedral_inv hd2 he2, inv_pow, inv_inv]
    rw [e1]
    exact T.inv_mem h5
  exact false_of_sq_mem hTab hj3 ho h6

theorem Sec6Ctx.false_of_center_mem_D (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n m) (hA8 : ¬ (n = 4 ∧ m = 1))
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) {d e : G} (hd : d ∈ classD T)
    (he : e ∈ classD T) {j : ℕ} (hj3 : 3 ≤ j) (ho : orderOf (d * e) = 2 * j)
    (hz : (d * e) ^ j ∈ classD T) : False := by
  obtain ⟨g, t, htT, -, hzg⟩ := hz
  have hd' : g * d * g⁻¹ ∈ classD T := classD_conj_mul hd g
  have he' : g * e * g⁻¹ ∈ classD T := classD_conj_mul he g
  have hconj : g * d * g⁻¹ * (g * e * g⁻¹) = g * (d * e) * g⁻¹ := by group
  have ho' : orderOf (g * d * g⁻¹ * (g * e * g⁻¹)) = 2 * j := by
    rw [hconj, ← ho]
    exact MulEquiv.orderOf_eq (MulAut.conj g) (d * e)
  have hzT' : (g * d * g⁻¹ * (g * e * g⁻¹)) ^ j ∈ T := by
    rw [hconj, conj_pow, hzg]
    have : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
    rw [this]
    exact htT
  exact hc.false_of_center_mem_T h1 h62 h63 hA8 hnat hd' he' hj3 ho' hzT'

end CFSG.CGT.Timmesfeld75
