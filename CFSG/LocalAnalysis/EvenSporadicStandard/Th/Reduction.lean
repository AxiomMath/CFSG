module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Transfer

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G}

omit [Finite G] in
theorem isPGroup_sup_of_commute {A B : Subgroup G} (hA : IsPGroup 2 A) (hB : IsPGroup 2 B)
    (hAB : B ≤ centralizer (A : Set G)) : IsPGroup 2 ↥(A ⊔ B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  rintro ⟨x, hx⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hAB hx
  obtain ⟨i, hi⟩ := IsPGroup.iff_orderOf.1 hA ⟨a, ha⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 hB ⟨b, hb⟩
  have hi' : orderOf a = 2 ^ i := by rw [← hi, Subgroup.orderOf_mk]
  have hj' : orderOf b = 2 ^ j := by rw [← hj, Subgroup.orderOf_mk]
  have hc : Commute a b := (mem_centralizer_iff.1 (hAB hb) a ha)
  have hdvd : orderOf (a * b) ∣ 2 ^ (max i j) := by
    refine hc.orderOf_mul_dvd_lcm.trans ?_
    rw [hi', hj']
    exact Nat.lcm_dvd (pow_dvd_pow 2 (le_max_left _ _)) (pow_dvd_pow 2 (le_max_right _ _))
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨k, by rw [Subgroup.orderOf_mk]; exact hk⟩

variable {SL : Subgroup G}

theorem ThCyc.le_centralizer_sylow (H : ThCyc G L R t) (hS : IsThSylow L SL) :
    R ≤ centralizer (SL : Set G) := fun _ hr =>
  mem_centralizer_iff.2 fun a ha => mem_centralizer_iff.1 (H.le_centralizer hr) a (hS.le ha)

theorem ThCyc.pgroup_sup (H : ThCyc G L R t) (hS : IsThSylow L SL) : IsPGroup 2 ↥(SL ⊔ R) :=
  isPGroup_sup_of_commute hS.pgroup H.pgroup (H.le_centralizer_sylow hS)

theorem ThCyc.sup_le_centralizer (H : ThCyc G L R t) (hS : IsThSylow L SL) :
    SL ⊔ R ≤ centralizer ({t} : Set G) := by
  rw [H.centralizer_eq]
  exact sup_le_sup_right hS.le R

theorem ThCyc.sup_max (H : ThCyc G L R t) (hS : IsThSylow L SL) {X : Subgroup G}
    (hXt : X ≤ centralizer ({t} : Set G)) (hX : IsPGroup 2 X) (hle : SL ⊔ R ≤ X) :
    X ≤ SL ⊔ R := by
  intro x hx
  have hxC := hXt hx
  rw [H.centralizer_eq] at hxC
  obtain ⟨l, hl, r, hr, rfl⟩ := exists_mul_of_mem_sup H.le_centralizer hxC
  have hrX : r ∈ X := hle (mem_sup_right hr)
  have hlX : l ∈ X := by
    have := X.mul_mem hx (X.inv_mem hrX)
    simpa using this
  have hXL : X ⊓ L ≤ SL :=
    hS.maximal (X ⊓ L) inf_le_right (hX.to_le inf_le_left)
      (le_inf (le_trans le_sup_left hle) hS.le)
  exact mul_mem_sup (hXL ⟨hlX, hl⟩) hr

theorem ThCyc.exists_mul_of_mem_sylow_sup (H : ThCyc G L R t) (hS : IsThSylow L SL) {s : G}
    (hs : s ∈ SL ⊔ R) : ∃ a ∈ SL, ∃ r ∈ R, s = a * r :=
  exists_mul_of_mem_sup (H.le_centralizer_sylow hS) hs

theorem ThCyc.not_sylow (H : ThCyc G L R t) (hS : IsThSylow L SL) :
    ¬ ∃ P : Sylow 2 G, (P : Subgroup G) = SL ⊔ R := by
  rintro ⟨P, hP⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := H.simple
  have hG := not_exists_normal_index_two_of_nonabelian H.nonabelian
  have hRSL := H.le_centralizer_sylow hS
  have hcomm : ∀ r ∈ R, ∀ a ∈ SL, r * a = a * r := fun r hr a ha =>
    (mem_centralizer_iff.1 (hRSL hr) a ha).symm
  have htS : t ∈ SL ⊔ R := mem_sup_right H.mem
  have htQ : t ∉ SL := by
    intro htl
    have : t ∈ L ⊓ R := ⟨hS.le htl, H.mem⟩
    rw [disjoint_iff.1 H.disjoint, mem_bot] at this
    have h2 := H.order_two
    rw [this, orderOf_one] at h2
    omega
  have ht2 : t ^ 2 = 1 := by rw [← H.order_two]; exact pow_orderOf_eq_one t
  have hQn : ∀ s ∈ SL ⊔ R, ∀ q ∈ SL, s * q * s⁻¹ ∈ SL := by
    intro s hs q hq
    obtain ⟨a, ha, r, hr, rfl⟩ := H.exists_mul_of_mem_sylow_sup hS hs
    have : a * r * q * (a * r)⁻¹ = a * q * a⁻¹ := by
      have hrq : r * q = q * r := hcomm r hr q hq
      calc a * r * q * (a * r)⁻¹ = a * (r * q) * r⁻¹ * a⁻¹ := by group
        _ = a * (q * r) * r⁻¹ * a⁻¹ := by rw [hrq]
        _ = a * q * a⁻¹ := by group
    rw [this]
    exact SL.mul_mem (SL.mul_mem ha hq) (SL.inv_mem ha)
  obtain ⟨b, hb⟩ := H.cyclic.exists_generator
  have hcyc : ∃ b' ∈ SL ⊔ R, ∀ s ∈ SL ⊔ R, ∃ k : ℤ, (b' ^ k)⁻¹ * s ∈ SL := by
    refine ⟨(b : G), mem_sup_right b.2, fun s hs => ?_⟩
    obtain ⟨a, ha, r, hr, rfl⟩ := H.exists_mul_of_mem_sylow_sup hS hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hb ⟨r, hr⟩)
    refine ⟨k, ?_⟩
    have hkr : (b : G) ^ k = r := congrArg Subtype.val hk
    have hbk : ((b : G) ^ k)⁻¹ * (a * r) = a := by
      rw [hkr]
      have := hcomm r hr a ha
      calc r⁻¹ * (a * r) = r⁻¹ * (r * a) := by rw [← this]
        _ = a := by group
    rw [hbk]
    exact ha
  have hSP : IsPGroup 2 ↥(SL ⊔ R) := H.pgroup_sup hS
  have hidx : ¬ 2 ∣ (SL ⊔ R).index := by
    rw [← hP]
    exact P.not_dvd_index
  obtain ⟨g, hg, -⟩ := exists_extremal_conj_of_cyclic hG hSP hidx hQn hcyc htS htQ ht2
  exact H.not_conj_mem g (hS.le hg)

theorem ThCyc.sylow_of_sq (H : ThCyc G L R t) (hS : IsThSylow L SL) {ρ : G} (hρ : ρ ∈ R)
    (hρt : ρ ^ 2 = t) : ∃ P : Sylow 2 G, (P : Subgroup G) = SL ⊔ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRSL := H.le_centralizer_sylow hS
  have hSP := H.pgroup_sup hS
  obtain ⟨P, hSP'⟩ := hSP.exists_le_sylow
  refine ⟨P, (eq_of_inf_normalizer_le P.isPGroup' hSP' ?_).symm⟩
  intro x hxP hxn
  set S := SL ⊔ R with hSdef
  have hx1 : ∀ s, s ∈ S ↔ x * s * x⁻¹ ∈ S := mem_normalizer_iff.1 hxn
  have hxinv : ∀ s ∈ S, x⁻¹ * s * x ∈ S := fun s hs =>
    (hx1 _).2 (by simpa [mul_assoc] using hs)
  have hRS : R ≤ S := le_sup_right
  have hρS : ρ ∈ S := hRS hρ
  have hcommSL : ∀ r ∈ R, ∀ a ∈ SL, r * a = a * r := fun r hr a ha =>
    (mem_centralizer_iff.1 (hRSL hr) a ha).symm
  have hρZ : ∀ s ∈ S, ρ * s = s * ρ := by
    intro s hs
    obtain ⟨a, ha, r, hr, rfl⟩ := H.exists_mul_of_mem_sylow_sup hS hs
    calc ρ * (a * r) = (ρ * a) * r := by rw [mul_assoc]
      _ = (a * ρ) * r := by rw [hcommSL ρ hρ a ha]
      _ = a * (ρ * r) := by rw [mul_assoc]
      _ = a * (r * ρ) := by rw [H.mul_comm_of_mem ρ hρ r hr]
      _ = (a * r) * ρ := by rw [mul_assoc]
  obtain ⟨σ, hσ⟩ : ∃ σ : G, σ = x * ρ * x⁻¹ := ⟨_, rfl⟩
  have hσS : σ ∈ S := by rw [hσ]; exact (hx1 ρ).1 hρS
  have hσZ : ∀ s ∈ S, σ * s = s * σ := by
    intro s hs
    have hs' := hxinv s hs
    have h1 := hρZ _ hs'
    calc σ * s = x * (ρ * (x⁻¹ * s * x)) * x⁻¹ := by rw [hσ]; group
      _ = x * ((x⁻¹ * s * x) * ρ) * x⁻¹ := by rw [h1]
      _ = s * σ := by rw [hσ]; group
  obtain ⟨a, ha, r', hr', hσar⟩ := H.exists_mul_of_mem_sylow_sup hS hσS
  have haZ : ∀ y ∈ SL, a * y = y * a := by
    intro y hy
    have hyS : y ∈ S := Subgroup.mem_sup_left hy
    have h1 := hσZ y hyS
    have ha' : a = σ * r'⁻¹ := by rw [hσar]; group
    have hr'y : r'⁻¹ * y = y * r'⁻¹ := hcommSL _ (R.inv_mem hr') y hy
    calc a * y = σ * (r'⁻¹ * y) := by rw [ha']; group
      _ = σ * (y * r'⁻¹) := by rw [hr'y]
      _ = (σ * y) * r'⁻¹ := by rw [mul_assoc]
      _ = (y * σ) * r'⁻¹ := by rw [h1]
      _ = y * (σ * r'⁻¹) := by rw [mul_assoc]
      _ = y * a := by rw [ha']
  have ha2 : a ^ 2 = 1 := hS.center a ha haZ
  have hσ2 : σ ^ 2 = r' ^ 2 := by
    have hcomm : a * r' = r' * a := (hcommSL r' hr' a ha).symm
    calc σ ^ 2 = (a * r') * (a * r') := by rw [hσar, sq]
      _ = a * (r' * a) * r' := by group
      _ = a * (a * r') * r' := by rw [← hcomm]
      _ = a ^ 2 * r' ^ 2 := by simp only [sq, mul_assoc]
      _ = r' ^ 2 := by rw [ha2, one_mul]
  have hxt : x * t * x⁻¹ = r' ^ 2 := by
    rw [← hσ2, hσ, ← hρt, conj_pow]
  have hxt2 : orderOf (x * t * x⁻¹) = 2 := by
    have := orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective t
    simpa using this.trans H.order_two
  have hxtR : x * t * x⁻¹ = t := by
    have hmem : x * t * x⁻¹ ∈ R := by rw [hxt]; exact R.pow_mem hr' 2
    have := H.cyclic
    have h1 : orderOf (⟨x * t * x⁻¹, hmem⟩ : R) = 2 := by rw [Subgroup.orderOf_mk]; exact hxt2
    have h2 : orderOf (⟨t, H.mem⟩ : R) = 2 := by rw [Subgroup.orderOf_mk]; exact H.order_two
    exact congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic h1 h2)
  have hxC : x ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc x * t = (x * t * x⁻¹) * x := by group
      _ = t * x := by rw [hxtR]
  have hX : IsPGroup 2 ↥(S ⊔ zpowers x) := P.isPGroup'.to_le (sup_le hSP' (zpowers_le.2 hxP))
  have hXt : S ⊔ zpowers x ≤ centralizer ({t} : Set G) :=
    sup_le (H.sup_le_centralizer hS) (zpowers_le.2 hxC)
  exact H.sup_max hS hXt hX le_sup_left (Subgroup.mem_sup_right (mem_zpowers x))

theorem exists_sq_eq_or_eq_zpowers {R : Subgroup G} (hR : IsPGroup 2 R) (hc : IsCyclic R)
    {t : G} (ht : t ∈ R) (ht2 : orderOf t = 2) : (∃ ρ ∈ R, ρ ^ 2 = t) ∨ R = zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := hc.exists_generator
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.1 hR g
  have ht' : orderOf (⟨t, ht⟩ : R) = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · right
    interval_cases m
    · exfalso
      rw [pow_zero, orderOf_eq_one_iff] at hm
      have : (⟨t, ht⟩ : R) = 1 := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨t, ht⟩)
        rw [← hk, hm, one_zpow]
      rw [this, orderOf_one] at ht'
      omega
    · have hg2 : orderOf g = 2 := by rw [hm, pow_one]
      have heq : (⟨t, ht⟩ : R) = g := eq_of_orderOf_eq_two_of_isCyclic ht' hg2
      refine le_antisymm (fun x hx => ?_) (zpowers_le.2 ht)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
      rw [← heq] at hk
      exact Subgroup.mem_zpowers_iff.2 ⟨k, congrArg Subtype.val hk⟩
  · left
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
    have hdvd : 2 ^ (n + 1) ∣ orderOf g := by rw [hm]; exact pow_dvd_pow 2 (by omega)
    have hord : orderOf (g ^ 2 ^ (n + 1)) = 2 := by
      rw [orderOf_pow_of_dvd (by positivity) hdvd, hm]
      rw [show n + 2 = (n + 1) + 1 by ring, pow_succ]
      exact Nat.mul_div_cancel_left 2 (by positivity)
    have heq : (⟨t, ht⟩ : R) = g ^ 2 ^ (n + 1) := eq_of_orderOf_eq_two_of_isCyclic ht' hord
    refine ⟨((g ^ 2 ^ n : R) : G), (g ^ 2 ^ n : R).2, ?_⟩
    have : (g ^ 2 ^ n) ^ 2 = (g ^ 2 ^ (n + 1) : R) := by
      rw [← pow_mul, pow_succ, mul_comm]
    rw [← Subgroup.coe_pow, this, ← heq]

theorem ThCyc.eq_zpowers (H : ThCyc G L R t) : R = zpowers t := by
  obtain ⟨SL, hS⟩ := H.exists_sylow
  rcases exists_sq_eq_or_eq_zpowers H.pgroup H.cyclic H.mem H.order_two with ⟨ρ, hρ, hρt⟩ | h
  · exact absurd (H.sylow_of_sq hS hρ hρt) (H.not_sylow hS)
  · exact h

theorem ThCyc.centralizer_eq_zpowers (H : ThCyc G L R t) :
    centralizer ({t} : Set G) = L ⊔ zpowers t := by
  rw [H.centralizer_eq, H.eq_zpowers]

end CFSG.EvenSporadicStandard.ThStd
