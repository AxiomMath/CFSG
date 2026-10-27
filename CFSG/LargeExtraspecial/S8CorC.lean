module

public import CFSG.LargeExtraspecial.S8CorB
public import CFSG.LargeExtraspecial.S5Five

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.Open

variable {X : Type*} [Group X]

theorem normal_of_sup_zpowers [Finite X] {U K : Subgroup X} (hU : U.Normal) (hKU : K ≤ U)
    (hKn : (K.subgroupOf U).Normal) (hKodd : Odd (Nat.card K)) {t : X} (htt : t * t = 1)
    (ht1 : t ≠ 1) (hUK : U = K ⊔ zpowers t) : K.Normal := by
  have htU : t ∈ U := hUK ▸ mem_sup_right (mem_zpowers t)
  have htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K := fun k hk => by
    have := hKn.conj_mem ⟨k, hKU hk⟩ (mem_subgroupOf.mpr hk) ⟨t, htU⟩
    rwa [mem_subgroupOf] at this
  have htnK : t ∉ K := fun h => by
    have h1 : orderOf t ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K h
    rw [orderOf_eq_prime (by rw [pow_two]; exact htt) ht1] at h1
    exact (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr h1)
  constructor
  intro k hk x
  set y := x * k * x⁻¹ with hy
  have hyU : y ∈ U := hU.conj_mem k (hKU hk) x
  have hyo : Odd (orderOf y) := by
    have h1 := orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective k
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    rw [← hy] at h1
    rw [h1]
    exact Odd.of_dvd_nat hKodd (Subgroup.orderOf_dvd_natCard K hk)
  rw [hUK] at hyU
  rcases (mem_sup_zpowers_iff htt htK).mp hyU with h | h
  · exact h
  · exfalso
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    have hy2 : y * y ∈ K := by
      have e : y * y = (y * t) * (t * (y * t) * t⁻¹) := by
        rw [hti]
        calc y * y = y * (t * t) * y * (t * t) := by rw [htt, mul_one, mul_one]
          _ = (y * t) * (t * (y * t) * t) := by group
      rw [e]
      exact K.mul_mem h (htK _ h)
    obtain ⟨m, hm⟩ := hyo
    have hyK : y ∈ K := by
      have e : y = (y * y) ^ (m + 1) := by
        rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf y + 1 by omega, pow_succ,
          pow_orderOf_eq_one, one_mul]
      rw [e]
      exact K.pow_mem hy2 _
    apply htnK
    have := K.mul_mem (K.inv_mem hyK) h
    rwa [inv_mul_cancel_left] at this

theorem commutator_sup_center_eq_top {G : Type*} [Group G] [Finite G]
    (hsimp : IsSimpleGroup (G ⧸ center G)) : commutator G ⊔ center G = ⊤ := by
  set π := QuotientGroup.mk' (center G) with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hperf : commutator (G ⧸ center G) = ⊤ := by
    have hn : (commutator (G ⧸ center G)).Normal := by
      rw [_root_.commutator_def]; infer_instance
    rcases @Subgroup.Normal.eq_bot_or_eq_top _ _ hsimp _ hn with h | h
    · exfalso
      have hcomm : IsMulCommutative (G ⧸ center G) :=
        ⟨⟨fun a b => by
          have := commutator_eq_bot_iff_le_centralizer.mp h (mem_top a)
          exact (mem_centralizer_iff.mp this b (mem_top b)).symm⟩⟩
      have hp := (Group.is_simple_iff_prime_card (α := G ⧸ center G)).mp hsimp
      have : Fact (Nat.card (G ⧸ center G)).Prime := ⟨hp⟩
      have hcyc : IsCyclic (G ⧸ center G) := isCyclic_of_prime_card rfl
      have hab : ∀ a b : G, a * b = b * a := fun a b =>
        (π.isMulCommutative_of_isCyclic_of_ker_le_center (by
          rw [hπ, QuotientGroup.ker_mk'])).is_comm.comm a b
      have htop : center G = ⊤ := eq_top_iff.mpr fun a _ =>
        mem_center_iff.mpr fun b => hab b a
      have : Subsingleton (G ⧸ center G) := by
        rw [htop]
        exact QuotientGroup.subsingleton_quotient_top
      exact (not_subsingleton _) this
    · exact h
  have hmap : (commutator G).map π = ⊤ := by
    rw [_root_.commutator_def, map_commutator, map_top_of_surjective π hsurj]
    rw [_root_.commutator_def] at hperf
    exact hperf
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := (hmap ▸ mem_top (π x) : π x ∈ (commutator G).map π)
  have hz : y⁻¹ * x ∈ center G := by
    rw [← QuotientGroup.ker_mk' (center G), MonoidHom.mem_ker, map_mul, map_inv, ← hπ, hyx,
      inv_mul_cancel]
  have e : x = y * (y⁻¹ * x) := by group
  rw [e]
  exact mul_mem (mem_sup_left hy) (mem_sup_right hz)

theorem commutator_eq_top_normalClosure [Finite X] {t : X} (htt : t * t = 1)
    (hZodd : ∀ z ∈ center ↥(normalClosure ({t} : Set X)), Odd (orderOf z))
    (hsimp : IsSimpleGroup
      (↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X)))) :
    commutator ↥(normalClosure ({t} : Set X)) = ⊤ := by
  set U := normalClosure ({t} : Set X) with hU
  set D := commutator ↥U with hD
  have hDZ := commutator_sup_center_eq_top hsimp
  have hconj : ∀ s : U, (s : X) ∈ Group.conjugatesOfSet ({t} : Set X) → s ∈ D := by
    intro s hs
    have hss : s * s = 1 := by
      obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hs
      rw [Set.mem_singleton_iff] at ha
      subst ha
      obtain ⟨c, hc⟩ := isConj_iff.mp hc
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one, ← hc]
      calc c * a * c⁻¹ * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
        _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
    obtain ⟨d, hd, z, hz, hdz⟩ := mem_sup_of_normal_right.mp (hDZ ▸ mem_top s)
    have hz2 : z * z ∈ D := by
      have hzc := mem_center_iff.mp hz
      have e : z * z = d⁻¹ * (s * d⁻¹ * s⁻¹) := by
        have hz' : z = d⁻¹ * s := by rw [← hdz]; group
        calc z * z = d⁻¹ * s * z := by rw [← hz']
          _ = d⁻¹ * (s * z) := by group
          _ = d⁻¹ * (s * (d⁻¹ * s)) := by rw [← hz']
          _ = d⁻¹ * (s * d⁻¹ * s⁻¹) * (s * s) := by group
          _ = d⁻¹ * (s * d⁻¹ * s⁻¹) := by rw [hss, mul_one]
      rw [e]
      have hn : D.Normal := by rw [hD, _root_.commutator_def]; infer_instance
      exact mul_mem (inv_mem hd) (hn.conj_mem _ (inv_mem hd) s)
    obtain ⟨m, hm⟩ := hZodd z hz
    have hzD : z ∈ D := by
      have e : z = (z * z) ^ (m + 1) := by
        rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf z + 1 by omega, pow_succ,
          pow_orderOf_eq_one, one_mul]
      rw [e]
      exact pow_mem hz2 _
    rw [← hdz]
    exact mul_mem hd hzD
  rw [eq_top_iff]
  rintro ⟨u, hu⟩ -
  have hle : U ≤ D.map U.subtype := by
    refine (closure_le (D.map U.subtype)).mpr ?_
    intro s hs
    have hsU : s ∈ U := conjugatesOfSet_subset_normalClosure hs
    exact ⟨⟨s, hsU⟩, hconj ⟨s, hsU⟩ hs, rfl⟩
  obtain ⟨v, hv, hvu⟩ := hle hu
  have : v = ⟨u, hu⟩ := Subtype.ext hvu
  rw [← this]
  exact hv

theorem normalClosure_eq_layer {t : X} (ht1 : t ≠ 1)
    (hperf : commutator ↥(normalClosure ({t} : Set X)) = ⊤)
    (hsimp : IsSimpleGroup
      (↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X))))
    (hE : CFSG.Open.IsQuasisimple (timmesfeldLayer X)) :
    normalClosure ({t} : Set X) = timmesfeldLayer X := by
  set U := normalClosure ({t} : Set X) with hU
  have hUn : U.Normal := normalClosure_normal
  have hcomp : CFSG.Open.IsComponentOf U ⊤ := by
    refine ⟨le_top, CFSG.Open.IsSubnormal.step le_top ⟨fun n hn x => ?_⟩
      (CFSG.Open.IsSubnormal.refl ⊤), ⟨hperf, hsimp⟩⟩
    rw [mem_subgroupOf] at hn ⊢
    exact hUn.conj_mem _ hn _
  have hle : U ≤ timmesfeldLayer X := le_sSup hcomp
  rcases S5.commute_or_eq_of_normalized hE hle fun a _ n hn => hUn.conj_mem n hn a with h | h
  · exfalso
    have hab : commutator ↥U = ⊥ := by
      rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
      intro a _
      exact mem_centralizer_iff.mpr fun b _ => Subtype.ext (h b b.2 a (hle a.2))
    rw [hperf] at hab
    have htU : t ∈ U := subset_normalClosure (Set.mem_singleton t)
    have : (⟨t, htU⟩ : U) ∈ (⊥ : Subgroup ↥U) := hab ▸ mem_top _
    exact ht1 (congrArg Subtype.val (Subgroup.mem_bot.mp this))
  · exact h

theorem comm_mem_centralizer_of_card_dvd_three [Finite X] {O : Subgroup X} [hO : O.Normal]
    (hO3 : Nat.card O ∣ 3) (a b : X) : a * b * a⁻¹ * b⁻¹ ∈ centralizer (O : Set X) := by
  have hcyc : IsCyclic O := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hO3 with h | h
    · have hbot : O = ⊥ := (Subgroup.eq_bot_iff_card O).mpr h
      subst hbot
      infer_instance
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact isCyclic_of_prime_card h
  have hcomm : ∀ φ ψ : MulAut O, φ * ψ = ψ * φ := by
    intro φ ψ
    apply (IsCyclic.mulAutMulEquiv (G := O)).injective
    rw [map_mul, map_mul, mul_comm]
  set f := (MulAut.conjNormal : X →* MulAut O) with hf
  have h1 : f (a * b * a⁻¹ * b⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm (f a) (f b)]
    group
  refine mem_centralizer_iff.mpr fun o ho => ?_
  have h2 := congrArg (fun φ : MulAut O => ((φ ⟨o, ho⟩ : O) : X)) h1
  simp only [hf, MulAut.conjNormal_apply, MulAut.one_apply] at h2
  calc o * (a * b * a⁻¹ * b⁻¹) = (a * b * a⁻¹ * b⁻¹) * o * (a * b * a⁻¹ * b⁻¹)⁻¹ *
      (a * b * a⁻¹ * b⁻¹) := by rw [h2]
    _ = a * b * a⁻¹ * b⁻¹ * o := by group

theorem commutator_commutator_centralizer_eq_bot [Finite X]
    (hO3 : Nat.card (timmesfeldOddCore X) ∣ 3)
    (hF : timmesfeldFStar X = timmesfeldOddCore X ⊔ timmesfeldLayer X)
    (hB : centralizer (timmesfeldFStar X : Set X) ≤ timmesfeldFStar X) :
    ⁅⁅centralizer (timmesfeldLayer X : Set X), centralizer (timmesfeldLayer X : Set X)⁆,
      ⁅centralizer (timmesfeldLayer X : Set X), centralizer (timmesfeldLayer X : Set X)⁆⁆ =
      ⊥ := by
  have : (timmesfeldOddCore X).Normal := S5.timmesfeldOddCore_normal X
  set C := centralizer (timmesfeldLayer X : Set X) with hC
  have h1 : ⁅C, C⁆ ≤ centralizer (timmesfeldFStar X : Set X) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hO := comm_mem_centralizer_of_card_dvd_three hO3 a b
    have hE : a * b * a⁻¹ * b⁻¹ ∈ C := mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    rw [hF]
    have hle : timmesfeldOddCore X ⊔ timmesfeldLayer X ≤
        centralizer ({a * b * a⁻¹ * b⁻¹} : Set X) := sup_le
      (fun o ho => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hO o ho))
      (fun e he => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hE e he))
    exact mem_centralizer_iff.mpr fun y hy =>
      mem_centralizer_singleton_iff.mp (hle hy)
  have h2 : ⁅centralizer (timmesfeldFStar X : Set X), centralizer (timmesfeldFStar X : Set X)⁆ =
      ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro a ha
    exact mem_centralizer_iff.mpr fun b hb => mem_centralizer_iff.mp ha b (hB hb)
  rw [eq_bot_iff, ← h2]
  exact commutator_mono h1 h1

theorem commutator_sup_le_sup_commutator {U A : Subgroup X} [U.Normal] :
    ⁅U ⊔ A, U ⊔ A⁆ ≤ U ⊔ ⁅A, A⁆ := by
  set π := QuotientGroup.mk' U with hπ
  have h1 : (⁅U ⊔ A, U ⊔ A⁆).map π ≤ (⁅A, A⁆).map π := by
    rw [map_commutator, map_commutator, Subgroup.map_sup, QuotientGroup.map_mk'_self,
      bot_sup_eq]
  have h2 := map_le_iff_le_comap.mp h1
  rw [comap_map_eq, QuotientGroup.ker_mk'] at h2
  exact h2.trans (le_of_eq (sup_comm _ _))

theorem derivedSeries_eq_top_of_simple {G : Type*} [Group G] (hsimp : IsSimpleGroup G)
    (hnab : ∃ x y : G, x * y ≠ y * x) (n : ℕ) : derivedSeries G n = ⊤ := by
  have hc : commutator G = ⊤ := by
    have hn : (commutator G).Normal := by rw [_root_.commutator_def]; infer_instance
    rcases @Subgroup.Normal.eq_bot_or_eq_top _ _ hsimp _ hn with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      apply hxy
      have := commutator_eq_bot_iff_le_centralizer.mp (_root_.commutator_def G ▸ h) (mem_top y)
      exact (mem_centralizer_iff.mp this x (mem_top x))
    · exact h
  induction n with
  | zero => rfl
  | succ n ih => rw [derivedSeries_succ, ih, ← _root_.commutator_def, hc]

theorem false_of_corB_list [Finite X] {t : X} (htt : t * t = 1) (ht1 : t ≠ 1)
    (hO2 : ∀ P : Subgroup X, CFSG.Open.IsSubnormal P ⊤ → IsPGroup 2 P → P = ⊥)
    (hO3 : Nat.card (timmesfeldOddCore X) ∣ 3)
    (hE : CFSG.Open.IsQuasisimple (timmesfeldLayer X))
    (hF : timmesfeldFStar X = timmesfeldOddCore X ⊔ timmesfeldLayer X)
    (hB : centralizer (timmesfeldFStar X : Set X) ≤ timmesfeldFStar X)
    (hsimpU : IsSimpleGroup
      (↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X))))
    (hder : ∃ k, derivedSeries X k ≤
      normalClosure ({t} : Set X) ⊔ centralizer (normalClosure ({t} : Set X) : Set X))
    (hsect : ∀ t' ∈ normalClosure ({t} : Set X), orderOf t' = 2 →
      (∃ u ∈ normalClosure ({t} : Set X), u * t' ≠ t' * u) →
      ∀ R N : Subgroup X, N ≤ R →
        R ≤ normalClosure ({t} : Set X) ⊓ centralizer ({t'} : Set X) →
          ∀ (_ : (N.subgroupOf R).Normal), IsSimpleGroup (↥R ⧸ N.subgroupOf R) →
            ∃ P : Sylow 2 (↥R ⧸ N.subgroupOf R),
              ∀ x ∈ (P : Subgroup (↥R ⧸ N.subgroupOf R)),
                ∀ y ∈ (P : Subgroup (↥R ⧸ N.subgroupOf R)), x * y = y * x)
    {R N : Subgroup X} (hRt : R ≤ centralizer ({t} : Set X)) (hNR : N ≤ R)
    [hNn : (N.subgroupOf R).Normal] (hsimp : IsSimpleGroup (↥R ⧸ N.subgroupOf R))
    (hnab : ∀ P : Sylow 2 (↥R ⧸ N.subgroupOf R), ∃ x ∈ (P : Subgroup (↥R ⧸ N.subgroupOf R)),
      ∃ y ∈ (P : Subgroup (↥R ⧸ N.subgroupOf R)), x * y ≠ y * x) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := normalClosure ({t} : Set X) with hU
  have hUn : U.Normal := normalClosure_normal
  have hZodd : ∀ z ∈ center ↥U, Odd (orderOf z) := by
    intro z hz
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have h0 : orderOf z ≠ 0 := (orderOf_pos z).ne'
    set w := z ^ (orderOf z / 2) with hw
    have hwo : orderOf w = 2 := orderOf_pow_orderOf_div h0 (even_iff_two_dvd.mp hev)
    have hwc : w ∈ center ↥U := pow_mem hz _
    have hwX : orderOf (w : X) = 2 := by rw [Subgroup.orderOf_coe, hwo]
    have hsub : CFSG.Open.IsSubnormal (zpowers (w : X)) ⊤ := by
      refine CFSG.Open.IsSubnormal.step (zpowers_le.mpr w.2) ⟨fun n hn u => ?_⟩
        (CFSG.Open.IsSubnormal.step le_top ⟨fun n hn x => ?_⟩ (CFSG.Open.IsSubnormal.refl ⊤))
      · rw [mem_subgroupOf] at hn ⊢
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn
        have hwu : (u : X) * w = w * u := congrArg Subtype.val ((mem_center_iff.mp hwc u))
        change (u : X) * n * (u : X)⁻¹ ∈ zpowers (w : X)
        rw [← hk, (Commute.zpow_right hwu k).eq, mul_inv_cancel_right]
        exact zpow_mem (mem_zpowers _) k
      · rw [mem_subgroupOf] at hn ⊢
        exact hUn.conj_mem _ hn _
    have h2 : IsPGroup 2 (zpowers (w : X)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hwX, pow_one])
    have hbot := hO2 _ hsub h2
    have : (w : X) ∈ zpowers (w : X) := mem_zpowers _
    rw [hbot, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hwX
    exact absurd hwX (by norm_num)
  have hperf := commutator_eq_top_normalClosure htt hZodd hsimpU
  have hUE := normalClosure_eq_layer ht1 hperf hsimpU hE
  have hCC := commutator_commutator_centralizer_eq_bot hO3 hF hB
  rw [← hUE] at hCC
  obtain ⟨k, hk⟩ := hder
  set C := centralizer (U : Set X) with hC
  have hXU : derivedSeries X (k + 2) ≤ U := by
    have h1 : derivedSeries X (k + 1) ≤ U ⊔ ⁅C, C⁆ := by
      rw [derivedSeries_succ]
      exact (commutator_mono hk hk).trans commutator_sup_le_sup_commutator
    rw [derivedSeries_succ]
    refine (commutator_mono h1 h1).trans (commutator_sup_le_sup_commutator.trans ?_)
    rw [hCC, sup_bot_eq]
  set R' := (derivedSeries ↥R (k + 2)).map R.subtype with hR'
  have hR'R : R' ≤ R := map_subtype_le _
  have hR'U : R' ≤ U ⊓ centralizer ({t} : Set X) :=
    le_inf ((map_derivedSeries_le_derivedSeries R.subtype (k + 2)).trans hXU)
      (hR'R.trans hRt)
  set N' := R' ⊓ N with hN'
  have hN'R' : N' ≤ R' := inf_le_left
  have hN'n : (N'.subgroupOf R').Normal := ⟨fun n hn r => by
    rw [mem_subgroupOf] at hn ⊢
    refine ⟨R'.mul_mem (R'.mul_mem r.2 hn.1) (R'.inv_mem r.2), ?_⟩
    have h1 := hNn.conj_mem ⟨n, hNR hn.2⟩ (mem_subgroupOf.mpr hn.2) ⟨r, hR'R r.2⟩
    rwa [mem_subgroupOf] at h1⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 (↥R ⧸ N.subgroupOf R)) := inferInstance
  obtain ⟨x₀, -, y₀, -, hxy₀⟩ := hnab P₀
  have hperfRN := derivedSeries_eq_top_of_simple hsimp ⟨x₀, y₀, hxy₀⟩ (k + 2)
  set ψ : R' →* (↥R ⧸ N.subgroupOf R) :=
    (QuotientGroup.mk' (N.subgroupOf R)).comp (Subgroup.inclusion hR'R) with hψ
  have hψs : Function.Surjective ψ := by
    intro q
    have hq : q ∈ (derivedSeries ↥R (k + 2)).map (QuotientGroup.mk' (N.subgroupOf R)) := by
      rw [map_derivedSeries_eq (QuotientGroup.mk'_surjective _), hperfRN]
      exact mem_top q
    obtain ⟨r, hr, rfl⟩ := hq
    exact ⟨⟨r, ⟨r, hr, rfl⟩⟩, rfl⟩
  have hker : ψ.ker = N'.subgroupOf R' := by
    ext r
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf]
    exact ⟨fun h => ⟨r.2, h⟩, fun h => h.2⟩
  have e : (↥R' ⧸ N'.subgroupOf R') ≃* (↥R ⧸ N.subgroupOf R) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  have hsimp' : IsSimpleGroup (↥R' ⧸ N'.subgroupOf R') := e.isSimpleGroup
  have htU : t ∈ U := subset_normalClosure (Set.mem_singleton t)
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have hnc : ∃ u ∈ U, u * t ≠ t * u := by
    by_contra hcon
    push Not at hcon
    have hc : (⟨t, htU⟩ : U) ∈ center ↥U :=
      mem_center_iff.mpr fun u => Subtype.ext (hcon u u.2)
    have := hZodd _ hc
    rw [Subgroup.orderOf_mk, hto] at this
    exact (Nat.not_odd_iff_even.mpr even_two) this
  obtain ⟨P, hP⟩ := hsect t htU hto hnc R' N' hN'R' hR'U hN'n hsimp'
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  have hx1 : x ∈ (P : Subgroup (↥R' ⧸ N'.subgroupOf R')).map e.toMonoidHom := hx
  have hy1 : y ∈ (P : Subgroup (↥R' ⧸ N'.subgroupOf R')).map e.toMonoidHom := hy
  obtain ⟨x', hx', rfl⟩ := hx1
  obtain ⟨y', hy', rfl⟩ := hy1
  apply hxy
  rw [← map_mul, ← map_mul, hP x' hx' y' hy']

end CFSG.LargeExtraspecial.S8
