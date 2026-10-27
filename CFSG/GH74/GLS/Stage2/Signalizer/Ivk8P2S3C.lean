module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S3A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoCov
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpLift
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S3

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Action

variable {G : Type} [Group G]

theorem isCyclic_of_le_sup {J V : Subgroup G} {x : G} (hxN : x ∈ normalizer (J : Set G))
    (hVN : V ≤ normalizer (J : Set G)) (hVx : V ≤ zpowers x ⊔ centralizer (J : Set G))
    (hVc : V ⊓ centralizer (J : Set G) = ⊥) : IsCyclic ↥V := by
  let N : Subgroup G := normalizer (J : Set G)
  let φ : ↥N →* MulAut ↥J := J.normalizerMonoidHom
  let x₀ : ↥N := ⟨x, hxN⟩
  let B : Subgroup ↥N := (zpowers (φ x₀)).comap φ
  have hCN : centralizer (J : Set G) ≤ N := Subgroup.centralizer_le_normalizer _
  have hker : ∀ n : ↥N, φ n = 1 ↔ (n : G) ∈ centralizer (J : Set G) := by
    intro n
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker]
    exact Iff.rfl
  have hsup : zpowers x ⊔ centralizer (J : Set G) ≤ B.map N.subtype := by
    refine sup_le ?_ ?_
    · exact Subgroup.zpowers_le.mpr ⟨x₀, Subgroup.mem_comap.mpr (Subgroup.mem_zpowers _), rfl⟩
    · intro c hc
      refine ⟨⟨c, hCN hc⟩, ?_, rfl⟩
      show φ ⟨c, hCN hc⟩ ∈ zpowers (φ x₀)
      rw [(hker ⟨c, hCN hc⟩).mpr hc]
      exact Subgroup.one_mem _
  have hV : ∀ v : ↥V, φ ⟨(v : G), hVN v.2⟩ ∈ zpowers (φ x₀) := by
    intro v
    obtain ⟨b, hb, hbv⟩ := hsup (hVx v.2)
    have : b = ⟨(v : G), hVN v.2⟩ := Subtype.ext hbv
    rw [this] at hb
    exact hb
  let f : ↥V →* ↥(zpowers (φ x₀)) :=
    (φ.comp (Subgroup.inclusion hVN)).codRestrict _ hV
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h1 : φ ⟨(v : G), hVN v.2⟩ = 1 := congrArg Subtype.val hv
    have h2 : (v : G) ∈ centralizer (J : Set G) := (hker _).mp h1
    have h3 : (v : G) ∈ V ⊓ centralizer (J : Set G) := ⟨v.2, h2⟩
    rw [hVc, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  exact isCyclic_of_injective f hf

theorem card_le_of_relIndex [Finite G] {J V P : Subgroup G} (hVP : V ≤ P)
    (hVc : V ⊓ centralizer (J : Set G) = ⊥)
    (h9 : (P ⊓ centralizer (J : Set G)).relIndex P = 9) : Nat.card ↥V ≤ 9 := by
  let K : Subgroup ↥P := (P ⊓ centralizer (J : Set G)).subgroupOf P
  let f : ↥V → ↥P ⧸ K := fun v => (QuotientGroup.mk (Subgroup.inclusion hVP v) : ↥P ⧸ K)
  have hf : Function.Injective f := by
    intro v w hvw
    have h1 : (Subgroup.inclusion hVP v)⁻¹ * Subgroup.inclusion hVP w ∈ K :=
      QuotientGroup.eq.mp hvw
    have h2 : ((v : G))⁻¹ * (w : G) ∈ P ⊓ centralizer (J : Set G) := h1
    have h3 : ((v : G))⁻¹ * (w : G) ∈ V ⊓ centralizer (J : Set G) :=
      ⟨V.mul_mem (V.inv_mem v.2) w.2, h2.2⟩
    rw [hVc, Subgroup.mem_bot, inv_mul_eq_one] at h3
    exact Subtype.ext h3
  have h4 : Nat.card ↥V ≤ Nat.card (↥P ⧸ K) := Nat.card_le_card_of_injective f hf
  have h5 : Nat.card (↥P ⧸ K) = 9 := by
    rw [← h9]
    rfl
  omega

end Action

section L34

variable {G : Type} [Group G] [Finite G]

theorem center_odd (hMin : MinIndexL34) (hInv : InvSec) {z : G}
    {k : Kind} {S : Subgroup G} (hctx : Stage2Ctx G z k S) {J : Subgroup G}
    (hq : IsQuasisimple ↥J) (hL : IsL34Quotient ↥J) : Odd (Nat.card ↥(center ↥J)) := by
  by_contra hodd
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heven : 2 ∣ Nat.card ↥(center ↥J) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥J)) 2 heven
  have hd2 : orderOf (((d : ↥J) : G)) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hd]
  have hle : J ≤ centralizer ({((d : ↥J) : G)} : Set G) := by
    intro j hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp d.2 ⟨j, hj⟩)
  obtain ⟨hs, hns⟩ := Gen.quasisimple_quot hq
  have hsec : IsSection (↥J ⧸ center ↥J) ↥(centralizer ({((d : ↥J) : G)} : Set G)) :=
    ⟨J.subgroupOf (centralizer ({((d : ↥J) : G)} : Set G)),
      (QuotientGroup.mk' (center ↥J)).comp (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom,
      (QuotientGroup.mk'_surjective _).comp (Subgroup.subgroupOfEquivOfLe hle).surjective⟩
  have := hs
  exact not_kindFactorAll_l34 hMin k hL (hInv G z k S hctx _ hd2 _ hns hsec)

theorem exists_elementaryAbelian_card {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    {k : ℕ} (hk : k ≤ pRank p Y) :
    ∃ E : Subgroup Y, IsElementaryAbelian p ↥E ∧ Nat.card ↥E = p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  have hbdd : BddAbove
      {r : ℕ | ∃ A : Subgroup Y, IsElementaryAbelian p ↥A ∧ Nat.card ↥A = p ^ r} := by
    refine ⟨Nat.card Y, ?_⟩
    rintro r ⟨B, -, hB⟩
    have h1 : r < p ^ r := Nat.lt_pow_self hp.one_lt
    have h2 : Nat.card ↥B ≤ Nat.card Y := Subgroup.card_le_card_group B
    omega
  have hbot : IsElementaryAbelian p (⊥ : Subgroup Y) := by
    have := IsElementaryAbelian.zpowers_of_pow_eq_one (p := p) (x := (1 : Y)) (one_pow p)
    rwa [Subgroup.zpowers_one_eq_bot] at this
  have hmem := Nat.sSup_mem (s := {r : ℕ | ∃ A : Subgroup Y, IsElementaryAbelian p ↥A ∧
    Nat.card ↥A = p ^ r}) ⟨0, ⊥, hbot, by simp⟩ hbdd
  obtain ⟨A, hA, hAc⟩ := hmem
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥A) p
    (show p ^ k ∣ Nat.card ↥A by rw [hAc]; exact pow_dvd_pow p hk)
  refine ⟨K.map A.subtype, isElementaryAbelian_of_le hA (Subgroup.map_subtype_le K), ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective, hK]

theorem le_pRank_of_card {p : ℕ} (hp : 1 < p) {H : Type} [Group H] [Finite H] (E : Subgroup H)
    (hE : IsElementaryAbelian p ↥E) {k : ℕ} (hk : Nat.card ↥E = p ^ k) : k ≤ pRank p H := by
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨E, hE, hk⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card H := Subgroup.card_le_card_group B

theorem isElementaryAbelian_of_injective {p : ℕ} {A Y : Type} [Group A] [Group Y]
    {E : Subgroup Y} (hE : IsElementaryAbelian p ↥E) (f : A →* Y) (hf : Function.Injective f)
    (hfE : ∀ a, f a ∈ E) : IsElementaryAbelian p A := by
  refine { toIsMulCommutative := ⟨⟨fun a b => hf ?_⟩⟩, exponent_dvd_p := ?_ }
  · rw [map_mul, map_mul]
    exact congrArg Subtype.val ((hE.toIsMulCommutative.is_comm).comm
      (⟨f a, hfE a⟩ : E) ⟨f b, hfE b⟩)
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => hf ?_
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) (f a) (hfE a)

theorem no_involution_centralizer {J : Subgroup G} (hZ : Odd (Nat.card ↥(center ↥J)))
    (hrk : 4 ≤ pRank 2 (↥J ⧸ center ↥J)) (hG : pRank 2 G ≤ 4) {c : G}
    (hc : c ∈ centralizer (J : Set G)) (hc2 : orderOf c = 2) : False := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Ē, hĒ, hĒc⟩ := exists_elementaryAbelian_card Nat.prime_two hrk
  obtain ⟨W, -, hWmap, hWN⟩ := exists_two_lift (center ↥J) hZ Ē
    (IsElementaryAbelian.isPGroup 2 ↥Ē)
  let f : ↥W →* ↥J ⧸ center ↥J := (QuotientGroup.mk' (center ↥J)).comp W.subtype
  have hfE : ∀ w : ↥W, f w ∈ Ē := fun w => by
    rw [← hWmap]; exact ⟨w, w.2, rfl⟩
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : (w : ↥J) ∈ center ↥J := (QuotientGroup.eq_one_iff _).mp hw
    have h3 : (w : ↥J) ∈ W ⊓ center ↥J := ⟨w.2, h1⟩
    rw [hWN, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hWel : IsElementaryAbelian 2 ↥W := isElementaryAbelian_of_injective hĒ f hf hfE
  have hWc : Nat.card ↥W = 2 ^ 4 := by
    rw [← hĒc]
    refine Nat.card_congr (Equiv.ofBijective (fun w : ↥W => (⟨f w, hfE w⟩ : ↥Ē)) ⟨?_, ?_⟩)
    · intro a b hab
      exact hf (congrArg Subtype.val hab)
    · rintro ⟨e, he⟩
      have : e ∈ W.map (QuotientGroup.mk' (center ↥J)) := hWmap ▸ he
      obtain ⟨w, hw, hwe⟩ := this
      exact ⟨⟨w, hw⟩, Subtype.ext hwe⟩
  let E : Subgroup G := W.map J.subtype
  have hEel : IsElementaryAbelian 2 ↥E := IsElementaryAbelian.map_subtype
  have hEc : Nat.card ↥E = 2 ^ 4 := by
    rw [Subgroup.card_map_of_injective J.subtype_injective, hWc]
  have hEJ : E ≤ J := Subgroup.map_subtype_le W
  have hcc : c ^ 2 = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hc2] at this
  have hCel : IsElementaryAbelian 2 ↥(zpowers c) := IsElementaryAbelian.zpowers_of_pow_eq_one hcc
  have hCE : zpowers c ≤ centralizer (E : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun e he => ?_)
    exact Subgroup.mem_centralizer_iff.mp hc e (hEJ he)
  have hTel : IsElementaryAbelian 2 ↥(E ⊔ zpowers c) := by
    have := hEel
    have := hCel
    exact IsElementaryAbelian.sup_of_le_centralizer hCE
  have hcE : c ∉ E := by
    intro hcE
    have hcJ : c ∈ J := hEJ hcE
    have hcz : (⟨c, hcJ⟩ : ↥J) ∈ center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro j
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc (j : G) j.2)
    have h1 : orderOf (⟨(⟨c, hcJ⟩ : ↥J), hcz⟩ : ↥(center ↥J)) = 2 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hc2]
    have h2 := orderOf_dvd_natCard (⟨(⟨c, hcJ⟩ : ↥J), hcz⟩ : ↥(center ↥J))
    rw [h1] at h2
    exact (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr h2)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp (IsElementaryAbelian.isPGroup 2 ↥(E ⊔ zpowers c))
  have hm5 : 5 ≤ m := by
    by_contra hlt
    have hle : Nat.card ↥(E ⊔ zpowers c) ≤ Nat.card ↥E := by
      rw [hm, hEc]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have heq : E = E ⊔ zpowers c := Subgroup.eq_of_le_of_card_ge le_sup_left hle
    exact hcE (heq ▸ (le_sup_right : zpowers c ≤ E ⊔ zpowers c) (Subgroup.mem_zpowers c))
  have := le_pRank_of_card one_lt_two (E ⊔ zpowers c) hTel hm
  omega

omit [Finite G] in
theorem Em_eq_of_comps {H J : Subgroup G} (hJ : IsCompIn H J)
    (h : ∀ K : Subgroup G, IsCompIn H K → K = J) : Em H = J := by
  have hlayer : layer ↥H = J.subgroupOf H := by
    refine le_antisymm (sSup_le fun K hK => ?_) (le_sSup hJ.2)
    have hsub : (K.map H.subtype).subgroupOf H = K :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective K
    have hKJ : K.map H.subtype = J :=
      h _ ⟨Subgroup.map_subtype_le K, by rw [hsub]; exact hK⟩
    rw [← hsub, hKJ]
  rw [Em_def, hlayer, Subgroup.subgroupOf_map_subtype, inf_of_le_left hJ.1]

theorem pPrimeCore_eq_center {J : Subgroup G} (hq : IsQuasisimple ↥J)
    (hZ : Odd (Nat.card ↥(center ↥J))) : pPrimeCore 2 ↥J = center ↥J := by
  refine le_antisymm ?_ (le_sSup ⟨inferInstance, ?_⟩)
  · rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (pPrimeCore_normal (p := 2) (G := ↥J))
      with htop | hle
    · exfalso
      have hcop : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥J)) := pPrimeCore_coprime_card
      rw [htop] at hcop
      have hodd : Odd (Nat.card ↥(⊤ : Subgroup ↥J)) := Nat.coprime_two_left.mp hcop
      rw [Subgroup.card_top] at hodd
      exact quasisimple_not_odd hq hodd
    · exact hle
  · exact Nat.coprime_two_left.mpr hZ

theorem lieModel_pPrimeCore {J : Subgroup G} (hq : IsQuasisimple ↥J)
    (hZ : Odd (Nat.card ↥(center ↥J))) (hL : IsL34Quotient ↥J) :
    LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 3 2 2 :=
  CFSG.GH74.lieModel_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (pPrimeCore_eq_center hq hZ).symm) hL

end L34

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S3
