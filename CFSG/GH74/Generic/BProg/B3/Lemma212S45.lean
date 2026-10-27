module

public import CFSG.GH74.Generic.BProg.B3.Obs
public import CFSG.GH74.Generic.BProg.B3.Lemma212Aux
public import CFSG.GH74.Generic.BProg.B1.PilotS4
public import CFSG.GH74.Generic.BProg.B2.TwoA7Geo

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS5 CFSG.GH74.Generic.BProg.B1.PilotS4
open scoped commutatorElement

namespace Lemma212S45

section Shape

theorem shape45_data
    {Kt : Type} [Group Kt] (h : QShape4 Kt ∨ QShape5 Kt) :
    ∃ n : ℕ, (∀ z : Kt, (∀ g : Kt, g * z = z * g) → z = 1) ∧
      ∀ u : Kt, orderOf u = 2 → ∃ L : Subgroup Kt, IsSplit n u L (centralizer ({u} : Set Kt)) := by
  rcases h with h4 | h5
  · obtain ⟨n, hn⟩ := splitGrp_of_qShape4 h4
    exact ⟨n, hn.center, hn.split⟩
  · obtain ⟨e5⟩ := h5
    have e : ↥(⊤ : Subgroup Kt) ≃* CFSG.Open.walterJ1 :=
      Subgroup.topEquiv.trans (e5.trans CFSG.Walter.walterJ1EquivNative.symm)
    have hY := SplitLike.of_equiv e
    refine ⟨60, fun z hz => hY.center z trivial (fun g _ => hz g), fun u hu => ?_⟩
    obtain ⟨L, -, hL⟩ := hY.split u trivial hu
    exact ⟨L, by simpa using hL⟩

end Shape

section KGroup

open CFSG.ComponentClassification

variable {G : Type} [Group G] [Finite G]

theorem pLayerOf_self {X K : Subgroup G} (hK : IsPCompIn 2 X K) : pLayerOf 2 K = K :=
  le_antisymm (sSup_le fun _ hL => hL.1) (le_sSup (Lemma212Aux.isPCompIn_of_le hK le_rfl hK.1))

theorem exists_mem_pLayerOf_of_split {K E : Subgroup G} {e : G} {n : ℕ}
    (hsplit : ∀ u : ↥K ⧸ pPrimeCore 2 ↥K, orderOf u = 2 →
      ∃ L : Subgroup (↥K ⧸ pPrimeCore 2 ↥K),
        IsSplit n u L (centralizer ({u} : Set (↥K ⧸ pPrimeCore 2 ↥K))))
    (hEK : E ≤ K) (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hE4 : Nat.card ↥E = 4) (heE : e ∈ E)
    (he1 : e ≠ 1) :
    ∃ f ∈ E, f ≠ 1 ∧ f ≠ e ∧ f ∈ pLayerOf 2 (K ⊓ centralizer ({e} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥K := pPrimeCore 2 ↥K with hN
  have hNodd : Odd (Nat.card N) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  set ψ : ↥K →* ↥K ⧸ N := QuotientGroup.mk' N with hψ
  have hsq : ∀ g ∈ E, g * g = 1 := fun g hg => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) g hg
    rwa [pow_two] at this
  set φ : ↥E →* ↥K ⧸ N := ψ.comp (Subgroup.inclusion hEK) with hφ
  set eE : ↥E := ⟨e, heE⟩ with heEdef
  have heE1 : eE ≠ 1 := fun h => he1 (congrArg Subtype.val h)
  have heEsq : eE * eE = 1 := Subtype.ext (hsq e heE)
  have hcommE : ∀ f g : ↥E, f * g = g * f := fun f g =>
    (IsMulCommutative.is_comm (M := ↥E)).comm f g
  have hφe1 : φ eE ≠ 1 := by
    intro h
    have h1 : (⟨e, hEK heE⟩ : ↥K) ∈ N := (QuotientGroup.eq_one_iff _).1 h
    have h2 : (⟨e, hEK heE⟩ : ↥K) * ⟨e, hEK heE⟩ = 1 := Subtype.ext (hsq e heE)
    exact he1 (congrArg Subtype.val (Th2.Bal.eq_one_of_sq_of_mem_pPrimeCore h2 h1))
  have hφ2 : orderOf (φ eE) = 2 :=
    orderOf_eq_prime (by rw [pow_two, ← map_mul, heEsq, map_one]) hφe1
  obtain ⟨L, hL⟩ := hsplit (φ eE) hφ2
  obtain ⟨f₀, hf₀1, hf₀e⟩ : ∃ f₀ : ↥E, f₀ ≠ 1 ∧ f₀ ≠ eE := by
    have hle : ¬ (⊤ : Subgroup ↥E) ≤ zpowers eE := by
      intro hle
      have h2 := Subgroup.card_le_of_le hle
      rw [Subgroup.card_top, Nat.card_zpowers,
        orderOf_eq_prime (by rw [pow_two]; exact heEsq) heE1, hE4] at h2
      omega
    obtain ⟨f₀, -, hf₀⟩ := IsConcreteLE.not_le_iff_exists.1 hle
    exact ⟨f₀, fun h => hf₀ (h ▸ one_mem _), fun h => hf₀ (h ▸ mem_zpowers eE)⟩
  have hφf₀ : φ f₀ ∈ centralizer ({φ eE} : Set (↥K ⧸ N)) :=
    Subgroup.mem_centralizer_singleton_iff.2 (by rw [← map_mul, ← map_mul, hcommE])
  have hmem : φ f₀ ∈ zpowers (φ eE) ⊔ L := hL.eq_sup ▸ hφf₀
  obtain ⟨f, hf1, hfe, hfL⟩ : ∃ f : ↥E, f ≠ 1 ∧ f ≠ eE ∧ φ f ∈ L := by
    rcases mem_sup_zpowers_of_two hL.ord hL.le_cent hmem with ⟨l, hl, hll⟩ | ⟨l, hl, hll⟩
    · exact ⟨f₀, hf₀1, hf₀e, hll ▸ hl⟩
    · refine ⟨f₀ * eE, ?_, ?_, ?_⟩
      · intro h
        apply hf₀e
        rw [eq_inv_of_mul_eq_one_left h]
        exact inv_eq_of_mul_eq_one_left heEsq
      · intro h
        apply hf₀1
        exact mul_right_cancel (h.trans (one_mul eE).symm)
      · rw [map_mul, hll]
        have hcl : φ eE * l = l * φ eE :=
          (Subgroup.mem_centralizer_singleton_iff.1 (hL.le_cent hl)).symm
        have h3 : φ eE * l * φ eE = l := by
          rw [hcl, mul_assoc, ← map_mul, heEsq, map_one, mul_one]
        rw [h3]
        exact hl
  set W : Subgroup G := K ⊓ centralizer ({e} : Set G) with hW
  have hWK : W ≤ K := inf_le_left
  set C : Subgroup (↥K ⧸ N) := centralizer ({φ eE} : Set (↥K ⧸ N)) with hC
  set ρ0 : ↥W →* ↥K ⧸ N := ψ.comp (Subgroup.inclusion hWK) with hρ0
  have hρ0C : ∀ w : ↥W, ρ0 w ∈ C := by
    intro w
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    have hw : (w : G) * e = e * (w : G) := Subgroup.mem_centralizer_singleton_iff.1 w.2.2
    show ψ (Subgroup.inclusion hWK w) * ψ (Subgroup.inclusion hEK eE) =
      ψ (Subgroup.inclusion hEK eE) * ψ (Subgroup.inclusion hWK w)
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext hw)
  set ρ : ↥W →* ↥C := ρ0.codRestrict C hρ0C with hρ
  have hordK : orderOf (⟨e, hEK heE⟩ : ↥K) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext (hsq e heE))
      (fun h => he1 (congrArg Subtype.val h))
  have hρsurj : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    have hy' : ∀ a ∈ zpowers (⟨e, hEK heE⟩ : ↥K), ψ a * y = y * ψ a := by
      intro a ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      have hcy : Commute (φ eE) y := (Subgroup.mem_centralizer_singleton_iff.1 hy).symm
      rw [map_zpow]
      exact (Commute.zpow_left hcy k).eq
    obtain ⟨g, hgψ, hgc⟩ := B1.centralizer_quotient_of_pGroup N hNodd
      (B1.isPGroup_two_zpowers_of_orderOf hordK) hy'
    have hge : (⟨e, hEK heE⟩ : ↥K) * g = g * ⟨e, hEK heE⟩ := hgc _ (mem_zpowers _)
    have hgW : (g : G) ∈ W := ⟨g.2, Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val hge).symm⟩
    exact ⟨⟨g, hgW⟩, Subtype.ext hgψ⟩
  have hker : Odd (Nat.card ρ.ker) := by
    have h1 : ¬ 2 ∣ Nat.card ρ0.ker := B1.not_two_dvd_card_ker_comp_mk (Subgroup.inclusion hWK)
      (Subgroup.inclusion_injective hWK) N hNodd
    have h2 : ρ.ker = ρ0.ker := MonoidHom.ker_codRestrict _ _ _
    rw [h2]
    exact Nat.odd_iff.2 (by omega)
  have hfW : (f : G) ∈ W := ⟨hEK f.2, Subgroup.mem_centralizer_singleton_iff.2
    (congrArg Subtype.val (hcommE f eE))⟩
  set fW : ↥W := ⟨(f : G), hfW⟩ with hfWdef
  have hfWsq : fW * fW = 1 := Subtype.ext (hsq f f.2)
  have hLC : L ≤ pLayerOf 2 C := le_sSup hL.isPCompIn
  have h1 : ρ fW ∈ TwoLayer.subgroup ↥C := by
    have hmem' : (ρ fW : ↥K ⧸ N) ∈ pLayerOf 2 C := hLC hfL
    rw [TwoThin.pLayerOf_two_eq_map] at hmem'
    obtain ⟨t, ht, htv⟩ := hmem'
    have : t = ρ fW := Subtype.ext htv
    rwa [this] at ht
  have h2 := Lemma212Aux.mem_twoLayer_of_map_mem ρ hρsurj hker hfWsq h1
  refine ⟨(f : G), f.2, fun h => hf1 (Subtype.ext h), fun h => hfe (Subtype.ext h), ?_⟩
  rw [hW, TwoThin.pLayerOf_two_eq_map]
  exact ⟨fW, h2, rfl⟩

end KGroup

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_centralizer_mul_eq {K : Subgroup G} {x e : G} (hK : K ≤ centralizer ({x} : Set G)) :
    K ⊓ centralizer ({e * x} : Set G) = K ⊓ centralizer ({e} : Set G) := by
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hgK, h⟩
    refine ⟨hgK, ?_⟩
    have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 (hK hgK)
    have h1 : g * e * x = e * g * x := by
      calc g * e * x = g * (e * x) := by rw [mul_assoc]
        _ = e * x * g := h
        _ = e * (x * g) := by rw [mul_assoc]
        _ = e * (g * x) := by rw [hgx]
        _ = e * g * x := by rw [mul_assoc]
    exact mul_right_cancel h1
  · rintro ⟨hgK, h⟩
    refine ⟨hgK, ?_⟩
    have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 (hK hgK)
    calc g * (e * x) = g * e * x := by rw [mul_assoc]
      _ = e * g * x := by rw [h]
      _ = e * (g * x) := by rw [mul_assoc]
      _ = e * (x * g) := by rw [hgx]
      _ = e * x * g := by rw [mul_assoc]

variable {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

theorem pLayerOf_le_of_balance (hx : orderOf x = 2) (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hax : a ∈ centralizer ({x} : Set G)) :
    pLayerOf 2 (K ⊓ centralizer ({a} : Set G)) ≤ pLayerOf 2 (centralizer ({a} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxa : x ∈ centralizer ({a} : Set G) := TwoThin.mem_centralizer_symm hax
  have hU : zpowers x ≤ centralizer ({a} : Set G) := Subgroup.zpowers_le.2 hxa
  have h1 := B2.SD.TwoA7Geo.pLayerOf_inf_centralizer_le_two hU
    (B1.isPGroup_two_zpowers_of_orderOf hx)
  have hcen : centralizer ({a} : Set G) ⊓ centralizer ((zpowers x : Subgroup G) : Set G) =
      centralizer ({x} : Set G) ⊓ centralizer ({a} : Set G) := by
    ext g
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨h2, h3⟩
      refine ⟨?_, h2⟩
      rw [Subgroup.mem_centralizer_iff] at h3 ⊢
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact h3 x (Subgroup.mem_zpowers x)
    · rintro ⟨h2, h3⟩
      refine ⟨h3, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at h2 ⊢
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (SetLike.mem_coe.1 hh)
      have hcx : x * g = g * x := h2 x (Set.mem_singleton x)
      exact (Commute.zpow_left (show Commute x g from hcx) k).eq
  rw [hcen] at h1
  have hsub := B1.isSubnormal_subgroupOf_inf (S := centralizer ({a} : Set G))
    (B1.isSubnormal_of_isPCompIn hK)
  refine le_trans (sSup_le fun L hL => le_sSup ?_) h1
  exact B1.isPCompIn_of_isSubnormal 2 (inf_le_inf_right _ hK.1) hsub hL

end Main

end Lemma212S45

section S45

open Lemma212S45

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

theorem lemma212a_s45
    (hc : Ctx21 G x K A a D J)
    (hP : QShape4 (↥K ⧸ pPrimeCore 2 ↥K) ∨ QShape5 (↥K ⧸ pPrimeCore 2 ↥K)) :
    ¬ pLayerOf 2 (K ⊓ centralizer ({a} : Set G)) ≤ centralizerSection J (pPrimeCoreOf 2 J) ∧
      J ≤ pumpUp 2 (pLayerOf 2 (K ⊓ centralizer ({a} : Set G))) a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hcen, hsplit⟩ := shape45_data hP
  have hx : orderOf x = 2 := hc.circ.1.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hc.circ.1.1.1.2.2
  have hKx : K ≤ centralizer ({x} : Set G) := hK.1
  obtain ⟨hAx, -, -, hcase⟩ := hc.src
  obtain ⟨E, hEK, hAE, hxE, hEel, hE4⟩ : ∃ E : Subgroup G, E ≤ K ∧ A = E ⊔ zpowers x ∧ x ∉ E ∧
      CFSG.IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 4 := by
    rcases hcase with ⟨-, h1⟩ | ⟨E, hEK, hAE, hxE, hEel, hE4, -⟩
    · exact (not_qShape1_of_center_trivial h1 hcen).elim
    · exact ⟨E, hEK, hAE, hxE, hEel, hE4⟩
  have ha2 : orderOf a = 2 := hc.obs.y_ord
  have ha1 : a ≠ 1 := fun h => by simp [h] at ha2
  have hcommEx : ∀ g ∈ E, ∀ h ∈ zpowers x, g * h = h * g := by
    intro g hg h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 (hKx (hEK hg))
    exact (Commute.zpow_right (show Commute g x from hgx) k).eq
  have haA : a ∈ E ⊔ zpowers x := hAE ▸ hc.a_mem
  obtain ⟨e, heE, z, hz, hae⟩ := mem_sup_of_commute hcommEx haA
  have hkey : ∃ f ∈ A, f ≠ 1 ∧ f ≠ a ∧ f ∈ pLayerOf 2 (K ⊓ centralizer ({a} : Set G)) := by
    by_cases he1 : e = 1
    · have hax : a = x := by
        rcases mem_zpowers_of_two hx hz with hz1 | hz1
        · exact absurd (by rw [hae, he1, hz1, mul_one]) ha1
        · rw [hae, he1, hz1, one_mul]
      obtain ⟨f, hfE, hf1⟩ : ∃ f ∈ E, f ≠ 1 := by
        by_contra h
        push Not at h
        have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 h
        rw [hbot, Subgroup.card_bot] at hE4
        omega
      refine ⟨f, hAE ▸ Subgroup.mem_sup_left hfE, hf1, fun h => hxE (hax ▸ h ▸ hfE), ?_⟩
      rw [hax, inf_eq_left.2 hKx, pLayerOf_self hK]
      exact hEK hfE
    · obtain ⟨f, hfE, hf1, hfe, hfI⟩ := exists_mem_pLayerOf_of_split hsplit hEK hEel hE4 heE he1
      rcases mem_zpowers_of_two hx hz with hz1 | hz1
      · have hae' : a = e := by rw [hae, hz1, mul_one]
        refine ⟨f, hAE ▸ Subgroup.mem_sup_left hfE, hf1, hae' ▸ hfe, ?_⟩
        rw [hae']
        exact hfI
      · have hae' : a = e * x := by rw [hae, hz1]
        refine ⟨f, hAE ▸ Subgroup.mem_sup_left hfE, hf1, fun h => hxE ?_, ?_⟩
        · have hx' : x = e⁻¹ * f := by rw [h, hae']; group
          rw [hx']
          exact E.mul_mem (E.inv_mem heE) hfE
        · rw [hae', inf_centralizer_mul_eq hKx]
          exact hfI
  obtain ⟨f, hfA, hf1, hfa, hfI⟩ := hkey
  have hnot : ¬ pLayerOf 2 (K ⊓ centralizer ({a} : Set G)) ≤
      centralizerSection J (pPrimeCoreOf 2 J) := by
    intro hle
    rcases hc.cA_eq f hfA (hle hfI) with h | h
    · exact hf1 h
    · exact hfa h
  refine ⟨hnot, ?_⟩
  have hbal := pLayerOf_le_of_balance hx hK (hAx hc.a_mem)
  have hII : pLayerOf 2 (K ⊓ centralizer ({a} : Set G)) ⊓ centralizer ({a} : Set G) =
      pLayerOf 2 (K ⊓ centralizer ({a} : Set G)) :=
    inf_eq_left.2 ((TwoThin.pLayerOf_le 2 _).trans inf_le_right)
  have hpp : pLayerOf 2 (pLayerOf 2 (K ⊓ centralizer ({a} : Set G)) ⊓ centralizer ({a} : Set G)) =
      pLayerOf 2 (K ⊓ centralizer ({a} : Set G)) := by
    rw [hII]
    exact Lemma212Aux.pLayerOf_pLayerOf _
  exact Lemma212Aux.le_pumpUp_of_not_le_cSec hc.obs.comp (by rw [hpp]; exact hbal)
    (by rw [hpp]; exact hnot)

end S45

end CFSG.GH74.Generic.BProg.B3
