module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinReduce
public import CFSG.CGT.PushingUpLit.SolKNA.R4.Perp25Swap
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpClass
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf2Conj
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinGraph
public import CFSG.ClassicalInvolution.Q3.Q3T7F25M7

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

namespace Perp25

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.T7F25.Asc77
open CFSG.ClassicalInvolution.Asc77 (IsFAut zStarOf WSet MuIsoE4 RSet IsSylow2In IsQuatSub
  mem_normalizer_iff_conjSub_eq isUniqueInvolution_of_mem_twinSet KPerp)
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)

section Engine

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem conjSub_le_of_mem {S X : Subgroup G} {s : G} (hs : s ∈ S) (hX : X ≤ S) :
    conjSub s X ≤ S := by
  intro x hx
  have h1 : s⁻¹ * x * s ∈ X := mem_conjSub_iff.mp hx
  have h2 := S.mul_mem (S.mul_mem hs (hX h1)) (S.inv_mem hs)
  have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
  rwa [e] at h2

theorem conjSub_sup_eq (h : Hyp25 Ω K K' W S R R' z t u₁ u₂) {s : G}
    (hs : s ∈ (S : Subgroup G)) : conjSub s (R ⊔ R') = R ⊔ R' := by
  have hΩ : HypOmegaGen Ω := h.std.1.stand.hyp
  have h1 := Q3.Q3CL.Thompson.conjSub_mem_RSet hΩ h.hR.1 s
  have h2 := Q3.Q3CL.Thompson.conjSub_mem_RSet hΩ h.hR'.1 s
  have hne : conjSub s R ≠ conjSub s R' := fun e => T7ER.ne_of_hyp25 h (conjSub_injective s e)
  have e : conjSub s (R ⊔ R') = conjSub s R ⊔ conjSub s R' := Subgroup.map_sup _ _ _
  rw [e]
  rcases h.hRS _ h1 (conjSub_le_of_mem hs h.hR.2.2) with e1 | e1 <;>
    rcases h.hRS _ h2 (conjSub_le_of_mem hs h.hR'.2.2) with e2 | e2
  · exact absurd (e1.trans e2.symm) hne
  · rw [e1, e2]
  · rw [e1, e2, sup_comm]
  · exact absurd (e1.trans e2.symm) hne

theorem c25_11_of_zStar_swap (h : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    (h6 : ∀ t' ∈ (S : Subgroup G), t' * t' = 1 → (∃ g : G, g * z * g⁻¹ = t') →
      conjSub t' R = R' → (¬ ∃ y : G, y * z * y⁻¹ = t' * z) →
      ∀ a : G, a * a = 1 → a ≠ 1 →
        a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) →
        a ∈ Subgroup.centralizer ({t'} : Set G) →
          z ∈ zStarOf (Subgroup.centralizer ({a} : Set G))) :
    (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z := by
  have hΩ : HypOmegaMod Ω := h.std.1.stand.hyp
  have hK : K ∈ Ω := h.std.1.stand.mem
  have hz : IsUniqueInvolution K z := h.std.1.hz
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK h.hR.1 h.hR.2.1
  have hzR : z ∈ R := T7C.mem_of_isSylow2In hΩ hK hRsyl hz
  set A : Subgroup G := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)
    with hAdef
  have hzS : z ∈ (S : Subgroup G) := h.hR.2.2 hzR
  have hzA : z ∈ A := by
    refine Subgroup.mem_inf.mpr ⟨hzS, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyS : y ∈ (S : Subgroup G) := by
      have : R ⊔ R' ≤ (S : Subgroup G) := sup_le h.hR.2.2 h.hR'.2.2
      exact this hy
    exact h.hzS y hyS
  have hnorm : ∀ s ∈ (S : Subgroup G), conjSub s A = A := by
    have key : ∀ s ∈ (S : Subgroup G), ∀ x ∈ A, s * x * s⁻¹ ∈ A := by
      intro s hs x hx
      have hx1 := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hs hx1.1)
        ((S : Subgroup G).inv_mem hs), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : s⁻¹ * y * s ∈ R ⊔ R' := by
        have h1 := conj_mem_conjSub (n := s⁻¹) hy
        rw [conjSub_sup_eq h ((S : Subgroup G).inv_mem hs), inv_inv] at h1
        exact h1
      have hxc := (Subgroup.mem_centralizer_iff.mp hx1.2) _ hy'
      calc y * (s * x * s⁻¹) = s * ((s⁻¹ * y * s) * x) * s⁻¹ := by group
        _ = s * (x * (s⁻¹ * y * s)) * s⁻¹ := by rw [hxc]
        _ = (s * x * s⁻¹) * y := by group
    intro s hs
    apply le_antisymm
    · intro x hx
      have h1 : s⁻¹ * x * s ∈ A := mem_conjSub_iff.mp hx
      have h2 := key s hs _ h1
      have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
      rwa [e] at h2
    · intro x hx
      have h1 := key s⁻¹ ((S : Subgroup G).inv_mem hs) x hx
      rw [inv_inv] at h1
      exact mem_conjSub_iff.mpr h1
  have hZ : ∀ t' ∈ (S : Subgroup G), t' * t' = 1 → (∃ g : G, g * z * g⁻¹ = t') →
      conjSub t' R = R' → (¬ ∃ y : G, y * z * y⁻¹ = t' * z) →
      ∀ a ∈ A ⊓ Subgroup.centralizer ({t'} : Set G), a ≠ 1 →
        z ∈ zStarOf (Subgroup.centralizer ({a} : Set G)) := by
    intro t' ht'S ht'2 hg ht'R hnf a hat ha1
    have ha : a ∈ A := hat.1
    have haS : a ∈ (S : Subgroup G) := ha.1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') ⟨a, haS⟩
    have hk' : orderOf a = 2 ^ k := by rw [← hk]; simp [← Subgroup.orderOf_coe]
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact ha1 (orderOf_eq_one_iff.mp (by simpa using hk'))
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    set i : G := a ^ (2 ^ j) with hi
    have hiA : i ∈ A := A.pow_mem ha _
    have hit : i ∈ Subgroup.centralizer ({t'} : Set G) := Subgroup.pow_mem _ hat.2 _
    have hdvd : 2 ^ j ∣ orderOf a := by rw [hk']; exact pow_dvd_pow 2 (Nat.le_succ j)
    have hio : orderOf i = 2 := by
      rw [hi, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hk', pow_succ,
        Nat.mul_div_cancel_left _ (pow_pos two_pos j)]
    have hi2 : i * i = 1 := by
      have := pow_orderOf_eq_one i
      rwa [hio, pow_two] at this
    have hi1 : i ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hio
      omega
    have h6' := h6 t' ht'S ht'2 hg ht'R hnf i hi2 hi1 hiA hit
    refine CFSG.ClassicalInvolution.Asc77.T7T.mem_zStarOf_of_le ?_ h6' ?_
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      exact ((Commute.pow_right (show Commute y a from hy) (2 ^ j)).eq)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (h.hzS a haS).symm
  exact T7T.c25_5_swap h A hzA inf_le_left hnorm hZ

theorem no_isFAut_of_inv (h : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    (h11 : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z)
    (hinv : ∀ a ∈ (S : Subgroup G), a * a = 1 → ¬ IsFAut R' a) :
    ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a := by
  obtain ⟨t', hT⟩ := T7T.exists_hyp25T h
  have hsq : ∀ a ∈ (S : Subgroup G), a * a ∈ Subgroup.zpowers z → ¬ IsFAut R' a := by
    intro a haS ha2 hF
    have haN : a ∈ Subgroup.normalizer (R' : Set G) := hF.1
    have hVle : R' ⊔ Subgroup.zpowers a ≤ (S : Subgroup G) :=
      sup_le hT.hR'S (Subgroup.zpowers_le.mpr haS)
    have hV2 : IsPGroup 2 ↥(R' ⊔ Subgroup.zpowers a) := S.isPGroup'.to_le hVle
    have hVn : R' ⊔ Subgroup.zpowers a ≤ Subgroup.normalizer (R' : Set G) :=
      sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr haN)
    have hVR : ∀ y ∈ R' ⊔ Subgroup.zpowers a, conjSub y R' = R' := fun y hy =>
      mem_normalizer_iff_conjSub_eq.mp (hVn hy)
    obtain ⟨r, hr, hb2, hbF⟩ := CFSG.ClassicalInvolution.Asc77.T7U.exists_involution_of_isFAut
      hT.hqR' hT.hzR' le_sup_left hV2 hVR (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)) hF ha2
    exact hinv (a * r) (Subgroup.mul_mem _ haS (hT.hR'S hr)) hb2 hbF
  have hres : ∀ a ∈ (S : Subgroup G), a * a ∈ R → ¬ IsFAut R' a := by
    intro a haS haR hF
    obtain ⟨a₁, ha₁S, ha₁sq, ha₁F⟩ := T7U.exists_sq_mem_zpowers_of_isFAut hT haS hF haR
    exact hsq a₁ ha₁S ha₁sq ha₁F
  intro a haS hF
  exact hres a haS (T7U.sq_mem_of_isFAut hT h11 hres haS hF) hF

theorem false_of_d8 {t' : G} (h : T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
    (hG : ∀ f : G →* Multiplicative (ZMod 2), (∀ u ∈ (R' : Set G), f u = 1) → f = 1)
    (h11 : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z)
    (h16 : ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a)
    (hlt : 2 * Nat.card ↥(R ⊔ R') < Nat.card ↥(CFSG.ClassicalInvolution.Asc77.T7F2.Nsub S R)) :
    False := by
  obtain ⟨a, haC, haR', ha2⟩ := T7F2.Hyp25T.exists_a h h11 h16 hlt
  have d := T7F2.Hyp25T.bdata h h11 h16 hlt haC haR'
  exact T7F2.false_of_fusion_gen (R' : Set G) hG S d.B d.relIndex_B a
    (CFSG.ClassicalInvolution.Asc77.T7F2.mem_Csub.mp haC).1
    (fun x hx => T7F2.Hyp25T.conj_not_mem_B h h11 d haC ha2 hx)
    (fun i x hx => T7F2.Hyp25T.pow_conj_mem_B h h11 d haC i hx)
    (fun u hu => ⟨h.hR'S hu, fun x hx => T7F2.Hyp25T.conj_mem_B_of_mem_R' h h11 d hu hx,
      fun i x hx => T7F2.Hyp25T.conj_mem_B_of_mem_R' h h11 d (R'.pow_mem hu _) hx⟩)

theorem tf4_of_hyp25 (h : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    (hG : ∀ f : G →* Multiplicative (ZMod 2), (∀ u ∈ (R' : Set G), f u = 1) → f = 1)
    (h11 : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z)
    (h16 : ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a) : TwoSubgroupsFourGenerated G := by
  obtain ⟨t', hT⟩ := T7T.exists_hyp25T h
  have h2 : ∃ t' ∈ (S : Subgroup G), (∃ g : G, g * z * g⁻¹ = t') ∧ conjSub t' R = R' :=
    c25_2_t_proved G Ω K K' W S R R' z t u₁ u₂ h
  have hnorm : Nat.card ↥((S : Subgroup G) ⊓ Subgroup.normalizer (R : Set G)) ≤
      2 * Nat.card ↥(R ⊔ R') := by
    by_contra hlt
    push Not at hlt
    exact false_of_d8 hT hG h11 h16 hlt
  rcases c25_19_of_sylow_at h h2 (c25_17_idx_of_norm_at h hnorm) with h4 | htf
  · exact T7Q.twoSubgroupsFourGenerated_of_index_four h h11 h16 h4
  · exact htf

theorem exists_conj_mem_sylow_ne_of_core (hOdd : CFSG.oddCore G = ⊥)
    (hCen : Subgroup.center G = ⊥) (S : Sylow 2 G) {z : G} (hzS : z ∈ (S : Subgroup G))
    (hzc : ∀ s ∈ (S : Subgroup G), s * z = z * s) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∃ g : G, g⁻¹ * z * g ∈ (S : Subgroup G) ∧ g⁻¹ * z * g ≠ z := by
  by_contra hcon
  push Not at hcon
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hord : orderOf (⟨z, hzS⟩ : (S : Subgroup G)) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hzord
  have hzZ : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (hzc s s.2)
  obtain ⟨hdec, -⟩ := CFSG.Adapters.glauberman_zStar S ⟨z, hzS⟩ hzZ hord hcon
  have hzcen : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, hc, k, hk, rfl⟩ := hdec g
    rw [hOdd, Subgroup.mem_bot] at hk
    subst hk
    rw [mul_one]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hc)
  rw [hCen, Subgroup.mem_bot] at hzcen
  exact hz1 hzcen

theorem hom_eq_one_of_sylow {Ω : Set (Subgroup G)} {K : Subgroup G}
    (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) (hgen : (⨆ J ∈ Ω, J) = ⊤)
    (hgen2 : ∀ J ∈ Ω, ∀ N : Subgroup G,
      (∀ x ∈ J, IsPGroup 2 ↥(Subgroup.zpowers x) → x ∈ N) → J ≤ N)
    {J R : Subgroup G} (hJ : J ∈ Ω) (hR : IsSylow2In R J)
    {A : Type*} [CommGroup A] (f : G →* A) (hf : ∀ x ∈ R, f x = 1) : f = 1 := by
  have hconj : ∀ (h : G) (x : G), x ∈ conjSub h R → f x = 1 := by
    intro h x hx
    have hx' : h⁻¹ * x * h ∈ R := mem_conjSub_iff.mp hx
    have := hf _ hx'
    simpa [map_mul, map_inv, mul_comm] using this
  have hmem : ∀ J' ∈ Ω, ∀ x ∈ J', f x = 1 := by
    intro J' hJ'
    obtain ⟨g₁, hg₁⟩ := htrans J' hJ'
    obtain ⟨g₂, hg₂⟩ := htrans J hJ
    have hJJ : conjSub (g₁ * g₂⁻¹) J = J' := by
      rw [← hg₁, ← hg₂]
      ext y
      simp only [mem_conjSub_iff]
      constructor <;> intro h <;> convert h using 1 <;> group
    have hP : IsSylow2In (conjSub (g₁ * g₂⁻¹) R) J' := hJJ ▸ hR.conj _
    have hker : J' ≤ f.ker := by
      refine hgen2 J' hJ' f.ker (fun x hx hx2 => ?_)
      obtain ⟨V, hV, hxV⟩ := IsSylow2In.exists_ge hx2 (Subgroup.zpowers_le.mpr hx)
      obtain ⟨c, -, hc⟩ := CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.exists_conjSub_eq_of_isSylow2In
        hP hV
      have hxV' : x ∈ conjSub c (conjSub (g₁ * g₂⁻¹) R) := hc ▸ hxV (Subgroup.mem_zpowers x)
      rw [mem_conjSub_iff] at hxV'
      have h1 := hconj (g₁ * g₂⁻¹) _ hxV'
      rw [MonoidHom.mem_ker]
      simpa [map_mul, map_inv, mul_comm] using h1
    exact fun x hx => MonoidHom.mem_ker.mp (hker hx)
  ext g
  have : g ∈ (⨆ J ∈ Ω, J) := hgen ▸ Subgroup.mem_top g
  have hle : (⨆ J ∈ Ω, J) ≤ f.ker := iSup₂_le fun J' hJ' x hx => hmem J' hJ' x hx
  simpa using hle this

theorem exists_hyp25_of_hyp23 (hOdd : CFSG.oddCore G = ⊥) (hCen : Subgroup.center G = ⊥)
    (hs : Hyp23 Ω K K' z) (hW : W ∈ WSet Ω) (hzW : z ∈ W)
    (hE4 : ∀ W' ∈ WSet Ω, MuIsoE4 Ω W') :
    ∃ (S : Sylow 2 G) (R R' : Subgroup G) (t u₁ u₂ : G), Hyp25 Ω K K' W S R R' z t u₁ u₂ := by
  have hset : Hyp23Setting Ω K K' z := hs.setting
  obtain ⟨S, R, R', hR, hR', hRS⟩ := c25_RS_proved G Ω K K' z hset W hW hzW hE4
  have hst : AscStand Ω K := hset.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hset.hK'.1
  have hz : IsUniqueInvolution K z := hset.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hset.hK'
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hR.1 hR.2.1
  have hR'syl : IsSylow2In R' K' := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK' hR'.1 hR'.2.1
  have hzR : z ∈ R := T7C.mem_of_isSylow2In hΩ hK hRsyl hz
  have hzR' : z ∈ R' := T7C.mem_of_isSylow2In hΩ hK' hR'syl hz'
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := by
    intro s hs'
    have h1 : conjSub s R ∈ RSet Ω := Q3.Q3CL.Thompson.conjSub_mem_RSet hΩ hR.1 s
    have h2 : conjSub s R ≤ (S : Subgroup G) := conjSub_le_of_mem hs' hR.2.2
    have hconj : s * z * s⁻¹ ∈ conjSub s R := conj_mem_conjSub hzR
    have hsq : (s * z * s⁻¹) * (s * z * s⁻¹) = 1 := by
      calc (s * z * s⁻¹) * (s * z * s⁻¹) = s * (z * z) * s⁻¹ := by group
        _ = 1 := by rw [hz.sq]; group
    have hne : s * z * s⁻¹ ≠ 1 := by
      intro he
      apply hz.ne_one
      calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
        _ = 1 := by rw [he]; group
    have hzz : s * z * s⁻¹ = z := by
      rcases hRS _ h1 h2 with e | e
      · rw [e] at hconj
        exact (hz.unique _ (hR.2.1 hconj) hsq).resolve_left hne
      · rw [e] at hconj
        exact (hz'.unique _ (hR'.2.1 hconj) hsq).resolve_left hne
    calc s * z = s * z * s⁻¹ * s := by group
      _ = z * s := by rw [hzz]
  obtain ⟨g, hgS, hgne⟩ := exists_conj_mem_sylow_ne_of_core hOdd hCen S (hR.2.2 hzR) hzS hz.sq
    hz.ne_one
  obtain ⟨u₁, hu₁R, o₁, hu₁n⟩ := T7C.exists_normal_zpowers_order_four hΩ hK hRsyl hz
  obtain ⟨u₂, hu₂R, o₂, hu₂n⟩ := T7C.exists_normal_zpowers_order_four hΩ hK' hR'syl hz'
  exact ⟨S, R, R', g⁻¹ * z * g, u₁, u₂, ⟨hs, hW, hzW, hE4, hR, hR', hRS, hzS,
    ⟨hgS, hgne, g⁻¹, by simp⟩, ⟨hu₁R, o₁, hu₁n⟩, ⟨hu₂R, o₂, hu₂n⟩⟩⟩

end Engine

end Perp25

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner

section Datum

theorem classicalClauseR {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    (hd : Q8TwinDatum R S t) (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R))) :
    Q3CL.ClassicalClause (CoreAssembly.conjClass (tightCore R)) where
  subnormal := by
    rintro K ⟨g, rfl⟩
    have hz := (Inner.isUniqueInvolution_core hd).conj g
    refine ⟨g * t * g⁻¹, hz.mem, ?_, isSubnormal_of_hypOmegaGen hΩ ⟨g, rfl⟩ hz⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  commOdd := by
    rintro J ⟨g, rfl⟩ u a b hu hu2 huu ha hb hau hbu
    simp only at hu ha hb ⊢
    rw [AscFusion.oddCoreOf_conjSub' g (tightCore R), mem_conjSub_iff]
    have hu' : g⁻¹ * u * g ∈ tightCore R := mem_conjSub_iff.mp hu
    have ha' : g⁻¹ * a * g ∈ tightCore R := mem_conjSub_iff.mp ha
    have hb' : g⁻¹ * b * g ∈ tightCore R := mem_conjSub_iff.mp hb
    have hu2' : IsPGroup 2 (Subgroup.zpowers (g⁻¹ * u * g)) := by
      have e : g⁻¹ * u * g = (MulAut.conj g⁻¹).toMonoidHom u := by simp
      rw [e, ← MonoidHom.map_zpowers]
      exact hu2.map _
    have huu' : (g⁻¹ * u * g) * (g⁻¹ * u * g) ≠ 1 := by
      intro h1
      apply huu
      have : u * u = g * ((g⁻¹ * u * g) * (g⁻¹ * u * g)) * g⁻¹ := by group
      rw [this, h1]; group
    have hau' : (g⁻¹ * a * g) * (g⁻¹ * u * g) = (g⁻¹ * u * g) * (g⁻¹ * a * g) := by
      calc (g⁻¹ * a * g) * (g⁻¹ * u * g) = g⁻¹ * (a * u) * g := by group
        _ = g⁻¹ * (u * a) * g := by rw [hau]
        _ = (g⁻¹ * u * g) * (g⁻¹ * a * g) := by group
    have hbu' : (g⁻¹ * b * g) * (g⁻¹ * u * g) = (g⁻¹ * u * g) * (g⁻¹ * b * g) := by
      calc (g⁻¹ * b * g) * (g⁻¹ * u * g) = g⁻¹ * (b * u) * g := by group
        _ = g⁻¹ * (u * b) * g := by rw [hbu]
        _ = (g⁻¹ * u * g) * (g⁻¹ * b * g) := by group
    have key := TwinPerp.commOdd_core hd hu' hu2' huu' ha' hb' hau' hbu'
    have e : g⁻¹ * (a * b * a⁻¹ * b⁻¹) * g =
        (g⁻¹ * a * g) * (g⁻¹ * b * g) * (g⁻¹ * a * g)⁻¹ * (g⁻¹ * b * g)⁻¹ := by group
    rw [e]
    exact key

end Datum

section Standing

structure PerpHypR (r n : ℕ) (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R)
    (t : Y) : Prop where
  core : TwinCoreHypR r n Y R S t
  disc : ¬ Disconnected.DConnected (CoreAssembly.conjClass (tightCore R))
  perp : KPerp (CoreAssembly.conjClass (tightCore R)) (tightCore R) =
    twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)

theorem twinCorePerpR_iff {r n : ℕ} :
    TwinCorePerpR r n ↔
      ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
        PerpHypR r n Y R S t → False :=
  ⟨fun h Y _ _ R S t hP => h Y R S t hP.core hP.disc hP.perp,
    fun h Y _ _ R S t hc hd hp => h Y R S t ⟨hc, hd, hp⟩⟩

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem PerpHypR.aEmpty_all (h : PerpHypR r n Y R S t) :
    ∀ J ∈ CoreAssembly.conjClass (tightCore R),
      AEmpty (CoreAssembly.conjClass (tightCore R)) J := by
  rintro J ⟨g, rfl⟩
  exact aEmpty_conj h.core.hyp.conjInvariant h.core.aEmpty g

theorem PerpHypR.partIHypG (h : PerpHypR r n Y R S t) :
    Q3CL.PartIHypG (CoreAssembly.conjClass (tightCore R)) :=
  ⟨h.core.hyp, classicalClauseR h.core.datum h.core.hyp, h.aEmpty_all⟩

theorem PerpHypR.ascStand (h : PerpHypR r n Y R S t) :
    T7F25.Asc77.AscStand (CoreAssembly.conjClass (tightCore R)) (tightCore R) where
  hyp := h.core.hyp
  aEmpty := h.aEmpty_all
  mem := CoreAssembly.mem_conjClass_self _
  trans := fun J hJ => by
    obtain ⟨g, hg⟩ := hJ
    exact ⟨g, hg⟩
  gen := iSup_conjClass_eq_top h.core.gen
  key := Q3.Q3CL.Sec7.l7_1Key h.partIHypG
  subn := fun _ hL _ hz =>
    (classicalClauseR h.core.datum h.core.hyp).isSubnormal_of_uniqueInvolution hL hz
  nine3 := Q3.Q3CL.l9_3 h.partIHypG

theorem PerpHypR.gen2 (h : PerpHypR r n Y R S t) :
    ∀ J ∈ CoreAssembly.conjClass (tightCore R), ∀ N : Subgroup Y,
      (∀ x ∈ J, IsPGroup 2 ↥(Subgroup.zpowers x) → x ∈ N) → J ≤ N := by
  intro J hJ N hN
  obtain ⟨g, hg⟩ := hJ
  have hJe : J = tightCore (conjSub g R) := by
    rw [← hg]; exact conjSub_tightCore R g
  have h2 : tightCore (conjSub g R) ≤ N := (Subgroup.closure_le _).mpr
    (fun x hx => hN x (by rw [hJe]; exact Subgroup.subset_closure hx) hx.2)
  rw [hJe]
  exact h2

theorem PerpHypR.hom_eq_one (h : PerpHypR r n Y R S t) {J R₁ : Subgroup Y}
    (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) (hR : IsSylow2In R₁ J) {A : Type*}
    [CommGroup A] (f : Y →* A) (hf : ∀ x ∈ R₁, f x = 1) : f = 1 :=
  Perp25.hom_eq_one_of_sylow (fun J hJ => by
      obtain ⟨g, hg⟩ := hJ
      exact ⟨g, hg⟩)
    (iSup_conjClass_eq_top h.core.gen) h.gen2 hJ hR f hf

theorem PerpHypR.center_eq_bot (h : PerpHypR r n Y R S t) : Subgroup.center Y = ⊥ := by
  haveI := h.core.simple
  have hC := CFSG.ClassicalInvolution.centralizer_genFittingFStar_eq_bot h.core.nonab
  refine le_antisymm (fun z hz => ?_) bot_le
  rw [← hC, Subgroup.mem_centralizer_iff]
  intro g _
  exact (Subgroup.mem_center_iff.mp hz) g

theorem PerpHypR.std7 (h : PerpHypR r n Y R S t) {K' : Subgroup Y}
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hne : K' ≠ tightCore R) :
    T7F25.Asc77.Std7 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' t :=
  ⟨h.ascStand, h.disc, Inner.isUniqueInvolution_core h.core.datum, hK', hne⟩

theorem PerpHypR.hyp23 (h : PerpHypR r n Y R S t) (h2 : TwinPerp.TwoTwins R) {K' : Subgroup Y}
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hne : K' ≠ tightCore R) :
    T7F25.Asc77.Hyp23 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' t :=
  ⟨h.std7 hK' hne, h.perp.trans (TwinPerp.twinSet_eq_pair h2 hK' hne)⟩

theorem PerpHypR.exists_hyp25 (h : PerpHypR r n Y R S t) (h2 : TwinPerp.TwoTwins R)
    (hE4 : ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), t ∈ W →
      MuIsoE4 (CoreAssembly.conjClass (tightCore R)) W) :
    ∃ (K' W : Subgroup Y) (S₁ : Sylow 2 Y) (R₁ R₂ : Subgroup Y) (t₁ u₁ u₂ : Y),
      T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t t₁
        u₁ u₂ := by
  obtain ⟨K', hK', hne⟩ := h.core.twin
  have hmem : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core h.core.datum
  have hall := TwinPerp.muIsoE4_all h.core.hyp hmem hz hE4
  obtain ⟨W, hW, hzW⟩ := TwinPerp.wz_of_hypOmegaGen h.core.hyp hmem hz
  obtain ⟨S₁, R₁, R₂, t₁, u₁, u₂, hyp⟩ := Perp25.exists_hyp25_of_hyp23 h.core.oddFree
    h.center_eq_bot (h.hyp23 h2 hK' hne) hW hzW hall
  exact ⟨K', W, S₁, R₁, R₂, t₁, u₁, u₂, hyp⟩

@[expose] def C25_6R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypR r n Y R S t →
    ∀ (K' W : Subgroup Y) (S₁ : Sylow 2 Y) (R₁ R₂ : Subgroup Y) (t₁ u₁ u₂ : Y),
      T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t t₁
        u₁ u₂ →
      ∀ t' ∈ (S₁ : Subgroup Y), t' * t' = 1 → (∃ g : Y, g * t * g⁻¹ = t') →
        conjSub t' R₁ = R₂ → (¬ ∃ y : Y, y * t * y⁻¹ = t' * t) →
      ∀ a : Y, a * a = 1 → a ≠ 1 →
        a ∈ (S₁ : Subgroup Y) ⊓ Subgroup.centralizer ((R₁ ⊔ R₂ : Subgroup Y) : Set Y) →
        a ∈ Subgroup.centralizer ({t'} : Set Y) →
          t ∈ zStarOf (Subgroup.centralizer ({a} : Set Y))

@[expose] def C25_16invR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypR r n Y R S t →
    ∀ (K' W : Subgroup Y) (S₁ : Sylow 2 Y) (R₁ R₂ : Subgroup Y) (t₁ u₁ u₂ : Y),
      T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t t₁
        u₁ u₂ →
      ∀ a ∈ (S₁ : Subgroup Y), a * a = 1 → ¬ IsFAut R₂ a

@[expose] def TwinPerp25AR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypR r n Y R S t → TwinPerp.TwoTwins R →
      (∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), t ∈ W →
        MuIsoE4 (CoreAssembly.conjClass (tightCore R)) W) →
      TwoSubgroupsFourGenerated ↥(genFittingFStar Y)

theorem c25_E4R_of_inputs {r n : ℕ} (h6 : C25_6R r n) (h16 : C25_16invR r n)
    {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    (h : PerpHypR r n Y R S t) (h2 : TwinPerp.TwoTwins R)
    (hE4 : ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), t ∈ W →
      MuIsoE4 (CoreAssembly.conjClass (tightCore R)) W) :
    TwoSubgroupsFourGenerated ↥(genFittingFStar Y) := by
  obtain ⟨K', W, S₁, R₁, R₂, t₁, u₁, u₂, hyp⟩ := h.exists_hyp25 h2 hE4
  have h11 := Perp25.c25_11_of_zStar_swap hyp fun t' ht'S ht'2 hg ht'R hnf a ha2 ha1 haA hat =>
    h6 Y R S t h K' W S₁ R₁ R₂ t₁ u₁ u₂ hyp t' ht'S ht'2 hg ht'R hnf a ha2 ha1 haA hat
  have h16' := Perp25.no_isFAut_of_inv hyp h11 fun a haS ha2 =>
    h16 Y R S t h K' W S₁ R₁ R₂ t₁ u₁ u₂ hyp a haS ha2
  have hK'Ω : K' ∈ CoreAssembly.conjClass (tightCore R) := hyp.std.1.hK'.1
  have hR₂ : IsSylow2In R₂ K' :=
    T7F25.Asc77.T7C.isSylow2In_of_mem_RSet_of_le hyp.std.1.stand.hyp hK'Ω hyp.hR'.1 hyp.hR'.2.1
  have htf : TwoSubgroupsFourGenerated Y :=
    Perp25.tf4_of_hyp25 hyp (fun f hf => h.hom_eq_one hK'Ω hR₂ f hf) h11 h16'
  exact twoSubgroupsFourGenerated_subgroup (genFittingFStar Y) htf

theorem twinPerp25AR_of_inputs {r n : ℕ} (h6 : C25_6R r n) (h16 : C25_16invR r n) :
    TwinPerp25AR r n :=
  fun _ _ _ _ _ _ h h2 hE4 => c25_E4R_of_inputs h6 h16 h h2 hE4

end Standing

end CFSG.CGT.PushingUpLit.SolKNA.R4
