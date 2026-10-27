module

public import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.ClaimY
public import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.Quot
public import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.Generation
public import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.Frame
public import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem comm_identity_aux {Q : Type*} [Group Q] (a q : Q) (ha : a * a = 1) :
    a * (q * a * q⁻¹ * a⁻¹) * a⁻¹ * (q * a * q⁻¹ * a⁻¹) = 1 := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  rw [ha']
  calc a * (q * a * q⁻¹ * a) * a * (q * a * q⁻¹ * a)
      = a * q * a * q⁻¹ * (a * a) * (q * a * q⁻¹ * a) := by group
    _ = a * q * a * q⁻¹ * (q * a * q⁻¹ * a) := by rw [ha, mul_one]
    _ = a * q * (a * a) * q⁻¹ * a := by group
    _ = a * q * 1 * q⁻¹ * a := by rw [ha]
    _ = a * a := by group
    _ = 1 := ha

private theorem centralizer_le_normalizer_self {Y : Subgroup G} :
    Subgroup.centralizer (Y : Set G) ≤ Subgroup.normalizer (Y : Set G) := by
  intro g hg
  have hc : ∀ x ∈ Y, x * g = g * x := fun x hx => Subgroup.mem_centralizer_iff.1 hg x hx
  apply Sec7.mem_normalizer_of_conj_mem
  · intro x hx
    have e : g * x * g⁻¹ = x := by rw [← hc x hx]; group
    rw [e]; exact hx
  · intro x hx
    have e : g⁻¹ * x * g = x := by
      calc g⁻¹ * x * g = g⁻¹ * (x * g) := by group
        _ = g⁻¹ * (g * x) := by rw [hc x hx]
        _ = x := by group
    rw [e]; exact hx

private theorem sup_conj_mem {k : G} {H J : Subgroup G}
    (hH : ∀ h ∈ H, k * h * k⁻¹ ∈ H ⊔ J) (hJ : ∀ j ∈ J, k * j * k⁻¹ ∈ H ⊔ J) :
    ∀ x ∈ H ⊔ J, k * x * k⁻¹ ∈ H ⊔ J := by
  intro x hx
  have hle : H ⊔ J ≤ (H ⊔ J).comap (MulAut.conj k).toMonoidHom :=
    sup_le (fun h hh => hH h hh) (fun j hj => hJ j hj)
  exact hle hx

private theorem mem_normalizer_sup_of_commute {R H J : Subgroup G} [(H.subgroupOf R).Normal]
    (hHn : R ≤ Subgroup.normalizer (H : Set G)) (hJR : J ≤ R) (g : ↥R)
    (hcomm : ∀ x : ↥R, (x : G) ∈ J →
      QuotientGroup.mk' (H.subgroupOf R) g * QuotientGroup.mk' (H.subgroupOf R) x =
        QuotientGroup.mk' (H.subgroupOf R) x * QuotientGroup.mk' (H.subgroupOf R) g) :
    (g : G) ∈ Subgroup.normalizer ((H ⊔ J : Subgroup G) : Set G) := by
  have hJ : ∀ j ∈ J, (g : G) * j * (g : G)⁻¹ * j⁻¹ ∈ H := fun j hj =>
    (mk_commute_iff g ⟨j, hJR hj⟩).1 (hcomm ⟨j, hJR hj⟩ hj)
  have hJ' : ∀ j ∈ J, (g : G)⁻¹ * j * ((g : G)⁻¹)⁻¹ * j⁻¹ ∈ H := by
    intro j hj
    have hc := hcomm ⟨j, hJR hj⟩ hj
    have hc' : QuotientGroup.mk' (H.subgroupOf R) g⁻¹ *
        QuotientGroup.mk' (H.subgroupOf R) ⟨j, hJR hj⟩ =
        QuotientGroup.mk' (H.subgroupOf R) ⟨j, hJR hj⟩ *
          QuotientGroup.mk' (H.subgroupOf R) g⁻¹ := by
      rw [map_inv]
      exact (Commute.inv_left (show Commute _ _ from hc)).eq
    have := (mk_commute_iff g⁻¹ ⟨j, hJR hj⟩).1 hc'
    simpa using this
  have hgH : ∀ h ∈ H, (g : G) * h * (g : G)⁻¹ ∈ H := fun h hh =>
    (Subgroup.mem_normalizer_iff.1 (hHn g.2) h).1 hh
  have hgH' : ∀ h ∈ H, (g : G)⁻¹ * h * ((g : G)⁻¹)⁻¹ ∈ H := fun h hh =>
    (Subgroup.mem_normalizer_iff.1 (hHn (R.inv_mem g.2)) h).1 hh
  have h1 : ∀ x ∈ H ⊔ J, (g : G) * x * (g : G)⁻¹ ∈ H ⊔ J :=
    sup_conj_mem (fun h hh => Subgroup.mem_sup_left (hgH h hh)) (fun j hj => by
      have e : (g : G) * j * (g : G)⁻¹ = ((g : G) * j * (g : G)⁻¹ * j⁻¹) * j := by group
      rw [e]; exact mul_mem (Subgroup.mem_sup_left (hJ j hj)) (Subgroup.mem_sup_right hj))
  have h2 : ∀ x ∈ H ⊔ J, (g : G)⁻¹ * x * (g : G) ∈ H ⊔ J := by
    intro x hx
    have := sup_conj_mem (k := (g : G)⁻¹) (fun h hh => Subgroup.mem_sup_left (hgH' h hh))
      (fun j hj => by
        have e : (g : G)⁻¹ * j * ((g : G)⁻¹)⁻¹ = ((g : G)⁻¹ * j * ((g : G)⁻¹)⁻¹ * j⁻¹) * j := by
          group
        rw [e]; exact mul_mem (Subgroup.mem_sup_left (hJ' j hj)) (Subgroup.mem_sup_right hj))
      x hx
    simpa using this
  exact Sec7.mem_normalizer_of_conj_mem h1 h2

private theorem commutator_mem_N1 {R S L H A₀ : Subgroup G} [(H.subgroupOf R).Normal]
    (hSR : S ≤ R) (hS : IsPGroup 2 S) (hLR : L ≤ R)
    (hLn : R ≤ Subgroup.normalizer (L : Set G)) (hHn : R ≤ Subgroup.normalizer (H : Set G))
    (hHS : H ≤ S) (h3 : ¬ 3 ∣ Nat.card R) (hZ : omegaOneZ (jOneOf S) ≤ H)
    (hXodd : Odd (Nat.card (bar R H L)))
    (hA₀S : A₀ ≤ S) (hA₀e : IsElemAbelian 2 A₀) (hA₀c : Nat.card A₀ = 2 ^ pRank 2 S)
    {E : Subgroup (↥R ⧸ H.subgroupOf R)} (hE : E ≤ bar R H A₀)
    (hcard : Nat.card (bar R H A₀) ≤ 2 * Nat.card E)
    {q a : ↥R ⧸ H.subgroupOf R} (hqX : q ∈ bar R H L)
    (hqC : q ∈ Subgroup.centralizer (E : Set (↥R ⧸ H.subgroupOf R))) (ha : a ∈ bar R H A₀) :
    q * a * q⁻¹ * a⁻¹ ∈ bar R H (Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) ⊓ R) := by
  have hA₀R : A₀ ≤ R := hA₀S.trans hSR
  have hAN : bar R H A₀ ≤
      Subgroup.normalizer ((bar R H L : Subgroup (↥R ⧸ H.subgroupOf R)) :
        Set (↥R ⧸ H.subgroupOf R)) :=
    bar_le_normalizer hA₀R hLR (hA₀R.trans hLn)
  have hcX : q * a * q⁻¹ * a⁻¹ ∈ bar R H L := by
    have h1 : a * q⁻¹ * a⁻¹ ∈ bar R H L :=
      (Subgroup.mem_normalizer_iff.1 (hAN ha) q⁻¹).1 (inv_mem hqX)
    have e : q * a * q⁻¹ * a⁻¹ = q * (a * q⁻¹ * a⁻¹) := by group
    rw [e]; exact mul_mem hqX h1
  have hcC : q * a * q⁻¹ * a⁻¹ ∈ Subgroup.centralizer (E : Set (↥R ⧸ H.subgroupOf R)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have heA : e ∈ bar R H A₀ := hE he
    have hq' : Commute e q := Subgroup.mem_centralizer_iff.1 hqC e he
    have ha' : Commute e a := (isElemAbelian_bar hA₀e).comm heA ha
    exact (((hq'.mul_right ha').mul_right hq'.inv_right).mul_right ha'.inv_right).eq
  have hcodd : Odd (orderOf (q * a * q⁻¹ * a⁻¹)) := by
    have h1 : orderOf (⟨q * a * q⁻¹ * a⁻¹, hcX⟩ : ↥(bar R H L)) ∣ Nat.card (bar R H L) :=
      orderOf_dvd_natCard _
    have h2 : orderOf (q * a * q⁻¹ * a⁻¹) =
        orderOf (⟨q * a * q⁻¹ * a⁻¹, hcX⟩ : ↥(bar R H L)) :=
      Subgroup.orderOf_coe (⟨q * a * q⁻¹ * a⁻¹, hcX⟩ : ↥(bar R H L))
    rw [h2]
    exact Odd.of_dvd_nat hXodd h1
  obtain ⟨y, _, hyodd, hyc⟩ := exists_odd_lift hLR hcX hcodd
  obtain ⟨r, hrA, hra⟩ := Subgroup.mem_map.1 ha
  have hrA' : (r : G) ∈ A₀ := Subgroup.mem_subgroupOf.1 hrA
  have hinv : (r : G) * (y : G) * (r : G)⁻¹ * (y : G) ∈ H := by
    have h1 : QuotientGroup.mk' (H.subgroupOf R) (r * y * r⁻¹ * y) = 1 := by
      simp only [map_mul, map_inv]
      rw [hra, hyc]
      exact comm_identity_aux a _ ((isElemAbelian_bar hA₀e).mul_self_eq_one ha)
    have h2 := (mk_eq_one_iff (r * y * r⁻¹ * y)).1 h1
    simpa using h2
  have hA₀y : ∀ x ∈ barPre R H A₀ E, x * (y : G) * x⁻¹ * (y : G)⁻¹ ∈ H := by
    intro x hx
    obtain ⟨_, hxR, hxE⟩ := mem_barPre_iff.1 hx
    have hcomm : QuotientGroup.mk' (H.subgroupOf R) ⟨x, hxR⟩ *
        QuotientGroup.mk' (H.subgroupOf R) y =
        QuotientGroup.mk' (H.subgroupOf R) y * QuotientGroup.mk' (H.subgroupOf R) ⟨x, hxR⟩ := by
      rw [hyc]
      exact (Subgroup.mem_centralizer_iff.1 hcC) _ hxE
    exact (mk_commute_iff ⟨x, hxR⟩ y).1 hcomm
  have hZ' : omegaOneZ (jOneOf S) ≤ barPre R H A₀ E := by
    intro z hz
    have hzA₀ : z ∈ A₀ := omegaOneZ_jOneOf_le hA₀S hA₀e hA₀c hz
    have hzR : z ∈ R := hSR (hA₀S hzA₀)
    rw [mem_barPre_iff]
    refine ⟨hzA₀, hzR, ?_⟩
    have h1 : QuotientGroup.mk' (H.subgroupOf R) ⟨z, hzR⟩ = 1 :=
      (mk_eq_one_iff ⟨z, hzR⟩).2 (hZ hz)
    rw [h1]; exact E.one_mem
  have h3' : ∀ g ∈ Subgroup.closure ((A₀ : Set G) ∪ {(y : G)}), ¬ 3 ∣ orderOf g := by
    intro g hg h3g
    have hcl : Subgroup.closure ((A₀ : Set G) ∪ {(y : G)}) ≤ R := by
      rw [Subgroup.closure_le]
      rintro x (hx | hx)
      · exact hA₀R hx
      · rw [Set.mem_singleton_iff.1 hx]; exact y.2
    have hgR : g ∈ R := hcl hg
    have hord : orderOf g = orderOf (⟨g, hgR⟩ : ↥R) := Subgroup.orderOf_coe (⟨g, hgR⟩ : ↥R)
    have hdvd : orderOf (⟨g, hgR⟩ : ↥R) ∣ Nat.card R := orderOf_dvd_natCard _
    rw [hord] at h3g
    exact h3 (h3g.trans hdvd)
  have hY := centralizer_omegaOneZ_jOneOf (S := S) (P := H) (A := A₀)
    (A₀ := barPre R H A₀ E) (y := (y : G)) (e := (r : G)) hS hHS hA₀S hA₀e hA₀c
    (barPre_le A₀ E) (card_le_two_mul_card_barPre hA₀R hE hcard) hyodd hrA'
    (fun x hx => hHn (hA₀R hx)) (hHn y.2) hinv hA₀y hZ' h3'
  have hYn : (y : G) ∈ Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) :=
    (centralizer_le_normalizer_self (Y := omegaOneZ (jOneOf S))) hY
  have hyN : QuotientGroup.mk' (H.subgroupOf R) y ∈
      bar R H (Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) ⊓ R) :=
    mk_mem_bar (Subgroup.mem_inf.2 ⟨hYn, y.2⟩)
  rw [hyc] at hyN
  exact hyN

theorem fac_zero_one_of_local {R S L H : Subgroup G}
    (h3 : ¬ 3 ∣ Nat.card R) (hSR : S ≤ R) (hS : IsPGroup 2 S)
    (hLR : L ≤ R) (hLn : R ≤ Subgroup.normalizer (L : Set G))
    (hH : H = S ⊓ L) (hHn : R ≤ Subgroup.normalizer (H : Set G))
    (hLodd : ¬ 2 ∣ H.relIndex L) (hRLS : (L : Set G) * (S : Set G) = (R : Set G))
    (hZ : omegaOneZ (jOneOf S) ≤ H) :
    Fac R (jOf S) (omegaOneZ (jOneOf S)) := by
  have hHS : H ≤ S := by rw [hH]; exact inf_le_left
  have hHL : H ≤ L := by rw [hH]; exact inf_le_right
  have hHR : H ≤ R := hHS.trans hSR
  haveI : (H.subgroupOf R).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hHR).2 hHn
  have hJS : jOf S ≤ S := Sec7.jOf_le S
  have hJR : jOf S ≤ R := hJS.trans hSR
  have hJ2 : IsPGroup 2 (jOf S) :=
    IsPGroup.of_equiv (IsPGroup.to_subgroup hS ((jOf S).subgroupOf S))
      (Subgroup.subgroupOfEquivOfLe hJS)
  have hSN1 : S ≤ Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) :=
    Sec7.le_normalizer_tripleOf (B := S) (T := S) Subgroup.le_normalizer 1
  have hHN1 : H ≤ Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) ⊓ R :=
    le_inf (hHS.trans hSN1) hHR
  have hXodd : Odd (Nat.card (bar R H L)) := odd_card_bar hLR hHL hLodd
  obtain ⟨𝒜, h𝒜def⟩ : ∃ 𝒜 : Set (Subgroup (↥R ⧸ H.subgroupOf R)),
      𝒜 = {Ā | ∃ A : Subgroup G, A ≤ S ∧ IsElemAbelian 2 A ∧ Nat.card A = 2 ^ pRank 2 S ∧
        Ā = bar R H A} := ⟨_, rfl⟩
  have hmem : ∀ Ā, Ā ∈ 𝒜 ↔ ∃ A : Subgroup G, A ≤ S ∧ IsElemAbelian 2 A ∧
      Nat.card A = 2 ^ pRank 2 S ∧ Ā = bar R H A := by
    intro Ā; rw [h𝒜def]; exact Iff.rfl
  obtain ⟨T, hTdef⟩ : ∃ T : Subgroup (↥R ⧸ H.subgroupOf R), T = ⨆ A ∈ 𝒜, A := ⟨_, rfl⟩
  have hBE : ∀ E : Subgroup G, E ≤ S → IsElemAbelian 2 E → Nat.card E = 2 ^ pRank 2 S →
      bar R H E ≤ T := by
    intro E hES hE hc
    rw [hTdef]
    exact le_iSup₂_of_le (bar R H E) ((hmem _).2 ⟨E, hES, hE, hc, rfl⟩) le_rfl
  have hTJ : T = bar R H (jOf S) := by
    refine le_antisymm ?_ ?_
    · rw [hTdef]
      refine iSup₂_le fun Ā hĀ => ?_
      obtain ⟨A, hAS, hAe, hAc, rfl⟩ := (hmem Ā).1 hĀ
      exact bar_mono (le_jOf hAS hAe hAc)
    · have hM : jOf S ≤ (T.comap (QuotientGroup.mk' (H.subgroupOf R))).map R.subtype := by
        refine iSup₂_le fun E hE => ?_
        intro e he
        have heR : e ∈ R := hSR (hE.1 he)
        refine Subgroup.mem_map.2 ⟨⟨e, heR⟩, ?_, rfl⟩
        refine Subgroup.mem_comap.2 ?_
        exact hBE E hE.1 hE.2.1
          (by rw [CFSG.SectionRank.pRank_coe_eq_openPRank]; exact hE.2.2)
          (mk_mem_bar (r := ⟨e, heR⟩) he)
      rintro q hq
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hq
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hM (Subgroup.mem_subgroupOf.1 hx))
      have hxy : y = x := Subtype.ext hyx
      subst hxy
      exact Subgroup.mem_comap.1 hy
  have h𝒜 : ∀ Ā ∈ 𝒜, IsElemAbelian 2 Ā := by
    intro Ā hĀ
    obtain ⟨A₀, _, hA₀e, _, rfl⟩ := (hmem Ā).1 hĀ
    exact isElemAbelian_bar hA₀e
  have h𝒜X : ∀ Ā ∈ 𝒜, Ā ≤ Subgroup.normalizer ((bar R H L : Subgroup _) : Set _) := by
    intro Ā hĀ
    obtain ⟨A₀, hA₀S, _, _, rfl⟩ := (hmem Ā).1 hĀ
    exact bar_le_normalizer (hA₀S.trans hSR) hLR (hA₀S.trans (hSR.trans hLn))
  have hT : IsPGroup 2 (⨆ A ∈ 𝒜, A : Subgroup (↥R ⧸ H.subgroupOf R)) := by
    rw [← hTdef, hTJ]; exact isPGroup_bar hJ2
  have h𝒜conj : ∀ t ∈ (⨆ A ∈ 𝒜, A : Subgroup (↥R ⧸ H.subgroupOf R)), ∀ Ā ∈ 𝒜,
      Ā.map (MulAut.conj t).toMonoidHom ∈ 𝒜 := by
    intro t ht Ā hĀ
    rw [← hTdef, hTJ] at ht
    obtain ⟨A₀, hA₀S, hA₀e, hA₀c, rfl⟩ := (hmem Ā).1 hĀ
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ht
    have hsS : (s : G) ∈ S := hJS (Subgroup.mem_subgroupOf.1 hs)
    rw [map_conj_bar (hA₀S.trans hSR) s]
    refine (hmem _).2 ⟨A₀.map (MulAut.conj (s : G)).toMonoidHom, ?_, hA₀e.map _, ?_, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      show (s : G) * x * (s : G)⁻¹ ∈ S
      exact S.mul_mem (S.mul_mem hsS (hA₀S hx)) (S.inv_mem hsS)
    · rw [Subgroup.card_map_of_injective (MulAut.conj (s : G)).injective]
      exact hA₀c
  have hN : ∀ Ā ∈ 𝒜, ∀ E : Subgroup (↥R ⧸ H.subgroupOf R), E ≤ Ā →
      Nat.card Ā ≤ 2 * Nat.card E →
      ∀ q ∈ bar R H L ⊓ Subgroup.centralizer (E : Set (↥R ⧸ H.subgroupOf R)), ∀ a ∈ Ā,
        q * a * q⁻¹ * a⁻¹ ∈ bar R H (Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) ⊓ R) := by
    intro Ā hĀ E hE hcard q hq a ha
    obtain ⟨A₀, hA₀S, hA₀e, hA₀c, rfl⟩ := (hmem Ā).1 hĀ
    obtain ⟨hqX, hqC⟩ := Subgroup.mem_inf.1 hq
    exact commutator_mem_N1 hSR hS hLR hLn hHn hHS h3 hZ hXodd hA₀S hA₀e hA₀c hE hcard hqX hqC ha
  have hkey := mem_centralizer_mul_of_commutators (X := bar R H L)
    (N := bar R H (Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) ⊓ R)) (𝒜 := 𝒜)
    hXodd h𝒜 h𝒜X hT h𝒜conj hN
  rw [← hTdef] at hkey
  have hL : ∀ l ∈ L, ∃ n₀ ∈ Subgroup.normalizer (jOf S : Set G) ⊓ R,
      ∃ m ∈ Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) ⊓ R, l = n₀ * m := by
    intro l hl
    have hlR : l ∈ R := hLR hl
    obtain ⟨c, ⟨hcX, hcC⟩, n, ⟨_, hnN⟩, hxcn⟩ :=
      hkey (QuotientGroup.mk' (H.subgroupOf R) ⟨l, hlR⟩) (mk_mem_bar (r := ⟨l, hlR⟩) hl)
    obtain ⟨l₀, hl₀, hl₀c⟩ := Subgroup.mem_map.1 hcX
    obtain ⟨n₁, hn₁, hn₁n⟩ := Subgroup.mem_map.1 hnN
    have hfin : QuotientGroup.mk' (H.subgroupOf R) (l₀ * n₁) =
        QuotientGroup.mk' (H.subgroupOf R) ⟨l, hlR⟩ := by
      rw [map_mul, hl₀c, hn₁n, hxcn]
    have hu : (l₀ * n₁)⁻¹ * ⟨l, hlR⟩ ∈ H.subgroupOf R := QuotientGroup.eq.1 hfin
    have hu' : (((l₀ * n₁)⁻¹ * ⟨l, hlR⟩ : ↥R) : G) ∈ H := Subgroup.mem_subgroupOf.1 hu
    have hcomm : ∀ x : ↥R, (x : G) ∈ jOf S →
        QuotientGroup.mk' (H.subgroupOf R) l₀ * QuotientGroup.mk' (H.subgroupOf R) x =
          QuotientGroup.mk' (H.subgroupOf R) x * QuotientGroup.mk' (H.subgroupOf R) l₀ := by
      intro x hx
      have hxT : QuotientGroup.mk' (H.subgroupOf R) x ∈ T := by
        rw [hTJ]; exact mk_mem_bar hx
      have hxc := (Subgroup.mem_centralizer_iff.1 hcC) _ hxT
      rw [hl₀c]; exact hxc.symm
    have hl₀N : (l₀ : G) ∈ Subgroup.normalizer ((H ⊔ jOf S : Subgroup G) : Set G) :=
      mem_normalizer_sup_of_commute hHn hJR l₀ hcomm
    have hTS : H ⊔ jOf S ≤ S := sup_le hHS hJS
    have hJT : jOf S ≤ H ⊔ jOf S := le_sup_right
    have hJeq : jOf (H ⊔ jOf S) = jOf S := jOf_eq_of_le hTS hJT
    have hl₀J : (l₀ : G) ∈ Subgroup.normalizer (jOf S : Set G) := by
      have h := Sec7.normalizer_le_normalizer_tripleOf (H ⊔ jOf S) 0 hl₀N
      rw [Sec7.tripleOf_zero, hJeq] at h
      exact h
    have hmN : (n₁ : G) * (((l₀ * n₁)⁻¹ * ⟨l, hlR⟩ : ↥R) : G) ∈
        Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) ⊓ R :=
      mul_mem (Subgroup.mem_subgroupOf.1 hn₁) (hHN1 hu')
    refine ⟨(l₀ : G), Subgroup.mem_inf.2 ⟨hl₀J, l₀.2⟩,
      (n₁ : G) * (((l₀ * n₁)⁻¹ * ⟨l, hlR⟩ : ↥R) : G), hmN, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  unfold Fac
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨n₀, hn₀, n₁, hn₁, rfl⟩
    exact mul_mem (Subgroup.mem_inf.1 hn₀).2 (Subgroup.mem_inf.1 hn₁).2
  · intro r hr
    rw [← hRLS] at hr
    obtain ⟨l, hl, s, hs, rfl⟩ := Set.mem_mul.1 hr
    obtain ⟨n₀, hn₀, m, hm, hlm⟩ := hL l hl
    refine Set.mem_mul.2 ⟨n₀, hn₀, m * s, ?_, ?_⟩
    · exact Subgroup.mem_inf.2 ⟨mul_mem (Subgroup.mem_inf.1 hm).1 (hSN1 hs),
        mul_mem (Subgroup.mem_inf.1 hm).2 (hSR hs)⟩
    · rw [hlm]; simp only [mul_assoc]

end CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1
