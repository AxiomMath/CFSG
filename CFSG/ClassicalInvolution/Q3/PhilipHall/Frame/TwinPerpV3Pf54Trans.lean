module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf53Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf51Comm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf52Aut

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open scoped commutatorElement
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Normal

variable {Y : Type} [Group Y]

theorem mem_normalizer_of_conj' {H : Subgroup Y} {x : Y} (h1 : ∀ y ∈ H, x * y * x⁻¹ ∈ H)
    (h2 : ∀ y ∈ H, x⁻¹ * y * x ∈ H) : x ∈ Subgroup.normalizer (H : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => h1 h hh, fun hh => ?_⟩
  have := h2 _ hh
  simpa [mul_assoc] using this

@[expose] def stabFam (V : Set (Subgroup Y)) : Subgroup Y :=
  ⨅ J ∈ V, Subgroup.normalizer (J : Set Y)

theorem mem_stabFam {V : Set (Subgroup Y)} {x : Y} :
    x ∈ stabFam V ↔ ∀ J ∈ V, x ∈ Subgroup.normalizer (J : Set Y) := by
  simp [stabFam, Subgroup.mem_iInf]

theorem conj_mem_normalizer {J : Subgroup Y} {c x : Y}
    (hx : x ∈ Subgroup.normalizer ((conjSub c⁻¹ J : Subgroup Y) : Set Y)) :
    c * x * c⁻¹ ∈ Subgroup.normalizer (J : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro j
  have key : ∀ y : Y, c * y * c⁻¹ ∈ J ↔ y ∈ conjSub c⁻¹ J := fun y => by
    rw [mem_conjSub_iff]; simp [mul_assoc]
  have h1 : j ∈ J ↔ c⁻¹ * j * c ∈ conjSub c⁻¹ J := by
    rw [← key]; simp [mul_assoc]
  have h2 := Subgroup.mem_normalizer_iff.mp hx (c⁻¹ * j * c)
  have h3 : (c * x * c⁻¹) * j * (c * x * c⁻¹)⁻¹ = c * (x * (c⁻¹ * j * c) * x⁻¹) * c⁻¹ := by group
  rw [h3, key, h1]
  exact h2

theorem normalizer_stab {V : Set (Subgroup Y)} {t : Y}
    (hV : ∀ c ∈ Subgroup.centralizer ({t} : Set Y), ∀ J ∈ V, conjSub c J ∈ V) :
    Subgroup.centralizer ({t} : Set Y) ≤
      Subgroup.normalizer ((stabFam V ⊓ Subgroup.centralizer ({t} : Set Y) : Subgroup Y) : Set Y) := by
  have key : ∀ c ∈ Subgroup.centralizer ({t} : Set Y), ∀ x ∈ stabFam V ⊓ Subgroup.centralizer ({t} : Set Y),
      c * x * c⁻¹ ∈ stabFam V ⊓ Subgroup.centralizer ({t} : Set Y) := by
    intro c hc x hx
    refine ⟨mem_stabFam.mpr fun J hJ => conj_mem_normalizer ?_, ?_⟩
    · exact (mem_stabFam.mp hx.1) _ (hV c⁻¹ (Subgroup.inv_mem _ hc) J hJ)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hx.2) (Subgroup.inv_mem _ hc)
  intro c hc
  exact mem_normalizer_of_conj' (key c hc) (fun y hy => by
    simpa using key c⁻¹ (Subgroup.inv_mem _ hc) y hy)

theorem conj_mem_centralizer {J : Subgroup Y} {h x : Y} (hh : h ∈ Subgroup.normalizer (J : Set Y))
    (hx : x ∈ Subgroup.centralizer (J : Set Y)) : h * x * h⁻¹ ∈ Subgroup.centralizer (J : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have h1 : h⁻¹ * j * h ∈ J := (mem_conj_iff_of_mem_normalizer hh j).mpr hj
  have h2 := Subgroup.mem_centralizer_iff.mp hx _ h1
  calc j * (h * x * h⁻¹) = h * ((h⁻¹ * j * h) * x) * h⁻¹ := by group
    _ = h * (x * (h⁻¹ * j * h)) * h⁻¹ := by rw [h2]
    _ = h * x * h⁻¹ * j := by group

end Normal

section Pair

variable {Y : Type} [Group Y] [Finite Y]

theorem quaternion_center_sq : ∀ q : QuaternionGroup 2, (∀ r : QuaternionGroup 2, q * r = r * q) → q ^ 2 = 1 := by
  decide +kernel

theorem sq_eq_one_of_central {K : Subgroup Y} (hq8 : Nonempty (↥K ≃* QuaternionGroup 2)) {c : Y}
    (hc : c ∈ K) (hcen : ∀ y ∈ K, c * y = y * c) : c * c = 1 := by
  obtain ⟨q⟩ := hq8
  have h := quaternion_center_sq (q ⟨c, hc⟩) (fun r => by
    obtain ⟨y, rfl⟩ := q.surjective r
    rw [← map_mul, ← map_mul]
    exact congrArg q (Subtype.ext (hcen y y.2)))
  have h2 : q (⟨c, hc⟩ * ⟨c, hc⟩) = 1 := by rw [map_mul, ← pow_two]; exact h
  have := q.injective (h2.trans q.map_one.symm)
  simpa using congrArg Subtype.val this

theorem odd_centralizes_twin {K K' : Subgroup Y} {t u₁ u₂ m : Y} {N : ℕ}
    (hz : IsUniqueInvolution K t) (hq8 : Nonempty (↥K ≃* QuaternionGroup 2))
    (hcomm : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x) (hu₁ : u₁ ∈ K) (hu₁4 : orderOf u₁ = 4) (hu₂ : u₂ ∈ K')
    (hmK : m ∈ Subgroup.normalizer (K : Set Y)) (hmK' : m ∈ Subgroup.normalizer (K' : Set Y))
    (hmt : m * t = t * m) (hmu : m * (u₁ * u₂) = (u₁ * u₂) * m) (hN : Odd N) (hmN : m ^ N = 1) :
    ∀ y ∈ K, m * y = y * m := by
  have hK8 : Nat.card ↥K = 8 := by
    obtain ⟨q⟩ := hq8
    rw [Nat.card_congr q.toEquiv, Pf51Comm.quaternion_card]
  have hu₁' : m * u₁ * m⁻¹ ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp hmK u₁).mp hu₁
    exact this
  have hu₂' : m * u₂ * m⁻¹ ∈ K' := (Subgroup.mem_normalizer_iff.mp hmK' u₂).mp hu₂
  have hprod : (m * u₁ * m⁻¹) * (m * u₂ * m⁻¹) = u₁ * u₂ := by
    have : m * (u₁ * u₂) * m⁻¹ = u₁ * u₂ := by rw [hmu]; group
    rw [← this]; group
  set c : Y := u₁⁻¹ * (m * u₁ * m⁻¹) with hc
  have hcK : c ∈ K := K.mul_mem (K.inv_mem hu₁) hu₁'
  have hcK' : c ∈ K' := by
    have : c = u₂ * (m * u₂ * m⁻¹)⁻¹ := by
      rw [hc]
      have h1 : m * u₁ * m⁻¹ = u₁ * u₂ * (m * u₂ * m⁻¹)⁻¹ := by
        rw [← hprod]; group
      rw [h1]; group
    rw [this]
    exact K'.mul_mem hu₂ (K'.inv_mem hu₂')
  have hcen : ∀ y ∈ K, c * y = y * c := fun y hy => hcomm y hy c hcK' |>.symm
  have hc2 : c * c = 1 := sq_eq_one_of_central hq8 hcK hcen
  have hc12 : c = 1 ∨ c = t := by
    rcases hz.unique c hcK hc2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hmc : m * c * m⁻¹ = c := by
    rcases hc12 with h | h
    · rw [h]; group
    · rw [h, hmt]; group
  have hconj : ∀ j : ℕ, m ^ j * u₁ * (m ^ j)⁻¹ = u₁ * c ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e1 : m ^ (j + 1) * u₁ * (m ^ (j + 1))⁻¹ = m * (m ^ j * u₁ * (m ^ j)⁻¹) * m⁻¹ := by
        rw [pow_succ']; group
      rw [e1, ih]
      have e2 : m * (u₁ * c ^ j) * m⁻¹ = (m * u₁ * m⁻¹) * (m * c * m⁻¹) ^ j := by
        rw [conj_pow]; group
      rw [e2, hmc]
      have e3 : m * u₁ * m⁻¹ = u₁ * c := by rw [hc]; group
      rw [e3, pow_succ']
      group
  have hcN : c ^ N = 1 := by
    have := hconj N
    rw [hmN] at this
    simpa using this.symm
  have hc1 : c = 1 := by
    rcases hc12 with h | h
    · exact h
    · exfalso
      rw [h] at hcN
      have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact hz.sq
      obtain ⟨k, rfl⟩ := hN
      have : t ^ (2 * k + 1) = t := by rw [pow_succ, pow_mul, ht2, one_pow, one_mul]
      rw [this] at hcN
      exact hz.ne_one hcN
  have hfix : m * u₁ * m⁻¹ = u₁ := by
    have : m * u₁ * m⁻¹ = u₁ * c := by rw [hc]; group
    rw [this, hc1, mul_one]
  exact centralizes_of_odd_fix hK8 hu₁ hu₁4 hmK hN hmN hfix

end Pair

section Lift

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {t u₁ u₂ u₃ : Y}
  {K K' K₃ K₄ M : Subgroup Y}

theorem odd_normalizes_twins (hΩ : HypOmegaGen Ω) (hz : IsUniqueInvolution K t)
    (hK : K ∈ Ω) (hKK' : K' ≠ K) (hK₃K : K₃ ≠ K) (hK₃K' : K₃ ≠ K') (h41 : K₄ ≠ K) (h42 : K₄ ≠ K')
    (hV : ∀ J ∈ twinSet Ω K, J = K ∨ J = K' ∨ J = K₃ ∨ J = K₄) (hK' : K' ∈ twinSet Ω K)
    {g : Y} (hgT : g ∈ Subgroup.centralizer ({t} : Set Y))
    (hg₃ : g ∈ Subgroup.normalizer (K₃ : Set Y)) (hg₄ : g ∈ Subgroup.normalizer (K₄ : Set Y))
    {N : ℕ} (hN : Odd N) (hgN : g ^ N = 1) :
    g ∈ Subgroup.normalizer (K : Set Y) ∧ g ∈ Subgroup.normalizer (K' : Set Y) := by
  have hgt : g * t * g⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hgT]; group
  have hinV : ∀ (c : Y), c * t * c⁻¹ = t → ∀ J ∈ twinSet Ω K, conjSub c J ∈ twinSet Ω K := by
    intro c hc J hJ
    refine ⟨hΩ.conjInvariant c J hJ.1, t, hz, ?_⟩
    have := (TwinSecXg.isUniqueInvolution_of_mem_twinSet hz hJ).conj c
    rwa [hc] at this
  have hK_V : K ∈ twinSet Ω K := ⟨hK, t, hz, hz⟩
  have h3 : conjSub g K₃ = K₃ := conjSub_eq_of_mem_normalizer hg₃
  have h4 : conjSub g K₄ = K₄ := conjSub_eq_of_mem_normalizer hg₄
  have hinj : Function.Injective (conjSub g : Subgroup Y → Subgroup Y) := CFSG.ClassicalInvolution.Generic.conjSub_injective g
  have hcases : ∀ J ∈ ({K, K'} : Set (Subgroup Y)), conjSub g J = K ∨ conjSub g J = K' := by
    intro J hJ
    have hJV : J ∈ twinSet Ω K := by
      rcases hJ with rfl | rfl
      · exact hK_V
      · exact hK'
    rcases hV _ (hinV g hgt J hJV) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have : J = K₃ := hinj (h.trans h3.symm)
      rcases hJ with rfl | rfl
      · exact hK₃K this.symm
      · exact hK₃K' this.symm
    · exfalso
      have : J = K₄ := hinj (h.trans h4.symm)
      rcases hJ with rfl | rfl
      · exact h41 this.symm
      · exact h42 this.symm
  have hσK := hcases K (Or.inl rfl)
  have hσK' := hcases K' (Or.inr rfl)
  have hKfix : conjSub g K = K := by
    rcases hσK with h | h
    · exact h
    · exfalso
      have hσK'K : conjSub g K' = K := by
        rcases hσK' with h' | h'
        · exact h'
        · exact absurd (hinj (h.trans h'.symm)) hKK'.symm
      have hiter : ∀ j : ℕ, conjSub (g ^ (2 * j)) K = K ∧ conjSub (g ^ (2 * j + 1)) K = K' := by
        intro j
        induction j with
        | zero => simpa using h
        | succ j ih =>
          have e1 : g ^ (2 * (j + 1)) = g * g ^ (2 * j + 1) := by rw [← pow_succ']; ring_nf
          have e2 : g ^ (2 * (j + 1) + 1) = g * g ^ (2 * (j + 1)) := by rw [← pow_succ']
          have a1 : conjSub (g ^ (2 * (j + 1))) K = K := by
            rw [e1, conjSub_mul, ih.2, hσK'K]
          refine ⟨a1, ?_⟩
          rw [e2, conjSub_mul, a1, h]
      obtain ⟨j, rfl⟩ := hN
      have := (hiter j).2
      rw [hgN, conjSub_one] at this
      exact hKK' this.symm
  refine ⟨(mem_normalizer_iff_conjSub_eq).mpr hKfix, ?_⟩
  refine (mem_normalizer_iff_conjSub_eq).mpr ?_
  rcases hσK' with h' | h'
  · exact absurd (hinj (hKfix.trans h'.symm)) hKK'.symm
  · exact h'


end Lift

section Gen

open scoped MatrixGroups

theorem exists_hom_of_equiv {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (he : Nonempty (↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, ZMod 3))) :
    ∃ φ : L →* SL(2, ZMod 3), Function.Surjective φ ∧ Odd (Nat.card φ.ker) := by
  obtain ⟨e⟩ := he
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore L)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore L))).ker =
      classicalInvolutionOddCore L := by
    ext x
    constructor
    · intro h
      have h1 : (QuotientGroup.mk' (classicalInvolutionOddCore L)) x = 1 :=
        e.map_eq_one_iff.mp h
      exact (QuotientGroup.eq_one_iff x).mp h1
    · intro h
      have h1 : (QuotientGroup.mk' (classicalInvolutionOddCore L)) x = 1 :=
        (QuotientGroup.eq_one_iff x).mpr h
      refine (MonoidHom.mem_ker).mpr ?_
      change e ((QuotientGroup.mk' (classicalInvolutionOddCore L)) x) = 1
      rw [h1]
      exact map_one e
  rw [hker]
  exact CFSG.ComponentClassification.OddCore.odd_card L

theorem le_of_forall_oddPrimePow_mem_of_equiv {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (he : Nonempty (↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, ZMod 3))) {H : Subgroup X}
    (hH : ∀ g ∈ L, ∀ p k : ℕ, p.Prime → p ≠ 2 → g ^ p ^ k = 1 → g ∈ H) : L ≤ H := by
  obtain ⟨φ, hφs, hφodd⟩ := exists_hom_of_equiv he
  set H' : Subgroup L := H.subgroupOf L with hH'def
  have hodd' : ∀ g : L, Odd (orderOf g) → g ∈ H' := by
    refine Q3T.mem_of_odd_orderOf H' fun g p k hp hp2 hg => ?_
    refine Subgroup.mem_subgroupOf.mpr (hH g g.2 p k hp hp2 ?_)
    have := congrArg (fun x : L => (x : X)) hg
    simpa using this
  have hker : φ.ker ≤ H' := by
    intro g hg
    refine hodd' g (hφodd.of_dvd_nat ?_)
    have := orderOf_dvd_natCard (⟨g, hg⟩ : φ.ker)
    rwa [Subgroup.orderOf_mk] at this
  have hthree : ∀ y : SL(2, ZMod 3), y ^ 3 = 1 → y ∈ H'.map φ := by
    intro y hy
    obtain ⟨g₀, rfl⟩ := hφs y
    obtain ⟨e, u, hu, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g₀).ne'
    refine ⟨g₀ ^ 4 ^ e, hodd' _ ?_, ?_⟩
    · have h4 : (4 : ℕ) ^ e = 2 ^ e * 2 ^ e := by rw [← mul_pow]; norm_num
      have hpow : (g₀ ^ 4 ^ e) ^ u = 1 := by
        rw [← pow_mul, h4, show 2 ^ e * 2 ^ e * u = 2 ^ e * u * 2 ^ e by ring, ← hn, pow_mul,
          pow_orderOf_eq_one, one_pow]
      exact hu.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
    · rw [map_pow]
      exact Q3T.pow_four_pow_of_pow_three hy e
  have htop : H'.map φ = ⊤ := by
    rw [eq_top_iff, ← Q3T.sl2_closure_three_eq_top, Subgroup.closure_le]
    exact fun y hy => hthree y hy
  intro g hg
  have hgφ : φ ⟨g, hg⟩ ∈ H'.map φ := htop ▸ Subgroup.mem_top _
  obtain ⟨h, hh, hhg⟩ := hgφ
  have hk : h⁻¹ * ⟨g, hg⟩ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hhg, inv_mul_cancel]
  have hmem : (⟨g, hg⟩ : L) ∈ H' := by
    have := H'.mul_mem hh (hker hk)
    simpa using this
  exact Subgroup.mem_subgroupOf.mp hmem


end Gen

section Main

open scoped MatrixGroups

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {t u₁ u₂ u₃ : Y}
  {K K' K₃ K₄ M : Subgroup Y}

set_option maxHeartbeats 1600000 in
open Pf51Comm in
theorem lift_isClassicalMember3
    (d : A7T22.Hyp22G Ω K K' K₃ t u₁ u₂ u₃) (hK₄ : K₄ ∈ twinSet Ω K) (h41 : K₄ ≠ K) (h42 : K₄ ≠ K')
    (hV : ∀ J ∈ twinSet Ω K, J = K ∨ J = K' ∨ J = K₃ ∨ J = K₄)
    (h2g : ∀ J ∈ Ω, IsPGroup 2 ↥J) (hq8 : ∀ J ∈ Ω, Nonempty (↥J ≃* QuaternionGroup 2))
    (hM : Q3NL.IsSectionMember3 (Subgroup.centralizer ({u₁ * u₂} : Set Y)) M t) (hK₃M : K₃ ≤ M)
    (hcomm₄ : ∀ a ∈ M, ∀ b ∈ K₄, a * b = b * a) (hOM : classicalInvolutionOddCore ↥M = ⊥) :
    IsClassicalMember3 M t := by
  classical
  have hΩ := d.hyp
  have hMle : M ≤ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({u₁ * u₂} : Set Y) :=
    isSubnormal_le hM.subnormal
  have hq8K := hq8 K d.mem
  have hq8K' := hq8 K' d.hK'.1
  have hq8K₃ := hq8 K₃ d.hK₃.1
  have hcommKK' : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x := fun x hx y hy =>
    (commute_of_trivialOnQuot (h2g K d.mem)
      (A7T22.le_trivialOnQuot_of_twin hΩ d.hK'.1 d.mem d.hne d.hzK' d.hz hy) hx).symm
  have hcommK'K : ∀ x ∈ K', ∀ y ∈ K, x * y = y * x := fun x hx y hy => (hcommKK' y hy x hx).symm
  obtain ⟨e'⟩ := hM.nonempty_equiv
  let e : ↥M ≃* SL(2, ZMod 3) :=
    ((QuotientGroup.quotientMulEquivOfEq hOM).trans QuotientGroup.quotientBot).symm.trans e'
  have hJeq := mem_iff_pow_four hK₃M hq8K₃ e
  have hN₃ : ∀ m ∈ M, m ∈ Subgroup.normalizer (K₃ : Set Y) := by
    intro m hm
    refine mem_normalizer_of_conj' (fun y hy => ?_) (fun y hy => ?_)
    · have hyM := hK₃M hy
      refine (hJeq _ (M.mul_mem (M.mul_mem hm hyM) (M.inv_mem hm))).mpr ?_
      have := (hJeq y hyM).mp hy
      rw [conj_pow, this]; group
    · have hyM := hK₃M hy
      have hm' := M.inv_mem hm
      have e1 : m⁻¹ * y * m = m⁻¹ * y * m⁻¹⁻¹ := by simp
      rw [e1]
      refine (hJeq _ (M.mul_mem (M.mul_mem hm' hyM) (M.inv_mem hm'))).mpr ?_
      have := (hJeq y hyM).mp hy
      rw [conj_pow, this]; group
  have hN₄ : ∀ m ∈ M, m ∈ Subgroup.normalizer (K₄ : Set Y) := by
    intro m hm
    refine mem_normalizer_of_conj' (fun y hy => ?_) (fun y hy => ?_)
    · have := hcomm₄ m hm y hy
      rw [this]; simpa using hy
    · have := hcomm₄ m hm y hy
      have e2 : m⁻¹ * y * m = y := by
        calc m⁻¹ * y * m = m⁻¹ * (y * m) := by group
          _ = m⁻¹ * (m * y) := by rw [this]
          _ = y := by group
      rw [e2]; exact hy
  have hodd : ∀ g ∈ M, ∀ p k : ℕ, p.Prime → p ≠ 2 → g ^ p ^ k = 1 →
      g ∈ Subgroup.centralizer (K : Set Y) ⊓ Subgroup.centralizer (K' : Set Y) := by
    intro g hg p k hp hp2 hgN
    have hNodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
    obtain ⟨hgK, hgK'⟩ := odd_normalizes_twins hΩ d.hz d.mem d.hne d.hK₃K d.hK₃K' h41 h42 hV d.hK'
      (hMle hg).1 (hN₃ g hg) (hN₄ g hg) hNodd hgN
    have hgu : g * (u₁ * u₂) = (u₁ * u₂) * g :=
      Subgroup.mem_centralizer_singleton_iff.mp (hMle hg).2
    have hgt : g * t = t * g := Subgroup.mem_centralizer_singleton_iff.mp (hMle hg).1
    have hgu' : g * (u₂ * u₁) = (u₂ * u₁) * g := by rw [← d.comm₁₂]; exact hgu
    refine ⟨?_, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      exact (odd_centralizes_twin d.hz hq8K hcommKK' d.hu₁.1 d.hu₁.2 d.hu₂.1 hgK hgK' hgt hgu
        hNodd hgN y hy).symm
    · refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      exact (odd_centralizes_twin d.hzK' hq8K' hcommK'K d.hu₂.1 d.hu₂.2 d.hu₁.1 hgK' hgK hgt hgu'
        hNodd hgN y hy).symm
  have hMcen : M ≤ Subgroup.centralizer (K : Set Y) ⊓ Subgroup.centralizer (K' : Set Y) :=
    le_of_forall_oddPrimePow_mem_of_equiv ⟨e'⟩ hodd
  set V : Set (Subgroup Y) := twinSet Ω K with hVdef
  have hVinv : ∀ c ∈ Subgroup.centralizer ({t} : Set Y), ∀ J ∈ V, conjSub c J ∈ V := by
    intro c hc J hJ
    have hct : c * t * c⁻¹ = t := by rw [Subgroup.mem_centralizer_singleton_iff.mp hc]; group
    refine ⟨hΩ.conjInvariant c J hJ.1, t, d.hz, ?_⟩
    have := (TwinSecXg.isUniqueInvolution_of_mem_twinSet d.hz hJ).conj c
    rwa [hct] at this
  set T₀ : Subgroup Y := stabFam V ⊓ Subgroup.centralizer ({t} : Set Y) with hT₀
  have hMT₀ : M ≤ T₀ := by
    intro m hm
    refine ⟨mem_stabFam.mpr fun J hJ => ?_, (hMle hm).1⟩
    rcases hV J hJ with rfl | rfl | rfl | rfl
    · exact Subgroup.centralizer_le_normalizer _ (hMcen hm).1
    · exact Subgroup.centralizer_le_normalizer _ (hMcen hm).2
    · exact hN₃ m hm
    · exact hN₄ m hm
  set R : Subgroup Y := T₀ ⊓ Subgroup.centralizer (K : Set Y) ⊓ Subgroup.centralizer (K' : Set Y) ⊓
    Subgroup.centralizer (K₄ : Set Y) with hR
  have hMR : M ≤ R := by
    intro m hm
    refine ⟨⟨⟨hMT₀ hm, (hMcen hm).1⟩, (hMcen hm).2⟩, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    exact (hcomm₄ m hm y hy).symm
  have hRle : R ≤ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    intro x hx
    refine ⟨hx.1.1.1.2, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h1 : u₁ * x = x * u₁ := Subgroup.mem_centralizer_iff.mp hx.1.1.2 u₁ d.hu₁.1
    have h2 : u₂ * x = x * u₂ := Subgroup.mem_centralizer_iff.mp hx.1.2 u₂ d.hu₂.1
    calc x * (u₁ * u₂) = (x * u₁) * u₂ := by group
      _ = (u₁ * x) * u₂ := by rw [h1]
      _ = u₁ * (x * u₂) := by group
      _ = u₁ * (u₂ * x) := by rw [h2]
      _ = (u₁ * u₂) * x := by group
  have hsubR : IsSubnormal M R :=
    Q3T6B.isSubnormal_of_le_of_le hM.subnormal hRle hMR
  have hT₀T : T₀ ≤ Subgroup.centralizer ({t} : Set Y) := inf_le_right
  have hT₀norm : (T₀.subgroupOf (Subgroup.centralizer ({t} : Set Y))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hT₀T).mpr (normalizer_stab hVinv)
  have hRT₀ : R ≤ T₀ := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hRkey : ∀ h ∈ T₀, ∀ x ∈ R, h * x * h⁻¹ ∈ R := by
    intro h hh x hx
    have hhN : ∀ J : Subgroup Y, h ∈ Subgroup.normalizer (J : Set Y) →
        ∀ x ∈ Subgroup.centralizer (J : Set Y), h * x * h⁻¹ ∈ Subgroup.centralizer (J : Set Y) :=
      fun J hJ x hx => conj_mem_centralizer hJ hx
    have hhS : ∀ J ∈ V, h ∈ Subgroup.normalizer (J : Set Y) := fun J hJ => mem_stabFam.mp hh.1 J hJ
    have hKV : K ∈ V := ⟨d.mem, t, d.hz, d.hz⟩
    have hK'V : K' ∈ V := d.hK'
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact T₀.mul_mem (T₀.mul_mem hh hx.1.1.1) (T₀.inv_mem hh)
    · exact hhN K (hhS K hKV) x hx.1.1.2
    · exact hhN K' (hhS K' hK'V) x hx.1.2
    · exact hhN K₄ (hhS K₄ hK₄) x hx.2
  have hRnorm : (R.subgroupOf T₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRT₀).mpr fun h hh =>
      mem_normalizer_of_conj' (hRkey h hh) (fun y hy => by
        simpa using hRkey h⁻¹ (T₀.inv_mem hh) y hy)
  have hRT : IsSubnormal R (Subgroup.centralizer ({t} : Set Y)) :=
    IsSubnormal.step hRT₀ hRnorm (isSubnormal_of_normal_subgroupOf hT₀T hT₀norm)
  exact ⟨hM.orderOf_eq_two, hM.mem, isSubnormal_trans hsubR hRT, hM.nonempty_equiv⟩

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
