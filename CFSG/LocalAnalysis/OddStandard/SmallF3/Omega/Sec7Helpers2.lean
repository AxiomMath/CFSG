module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts3
public import CFSG.LocalAnalysis.ZStar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts
public import CFSG.Walter.AStar.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G]
theorem isConj_iff_inv_mul {a b : G} : IsConj a b ↔ ∃ g : G, g⁻¹ * a * g = b := by
  rw [isConj_iff]
  constructor <;> rintro ⟨c, hc⟩ <;> exact ⟨c⁻¹, by rwa [inv_inv]⟩
theorem isConj_of_mem_conjClassIn {H : Subgroup G} {x y : G} (h : y ∈ conjClassIn H x) :
    IsConj x y := by
  obtain ⟨k, _, rfl⟩ := h
  exact isConj_iff_inv_mul.mpr ⟨k⁻¹, by rw [inv_inv]⟩
theorem conjugate_conjugate_inv (L : Subgroup G) (g : G) :
    CFSG.conjugate (CFSG.conjugate L g) g⁻¹ = L := by
  have h : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  simp only [CFSG.conjugate, inv_inv, Subgroup.map_map, h, Subgroup.map_id]
theorem mem_centralizer_conjugate {L : Subgroup G} {c : G} (hc : c ∈ centralizer (L : Set G))
    (g : G) : g⁻¹ * c * g ∈ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  change x ∈ CFSG.conjugate L g at hx
  rw [mem_conjugate_iff] at hx
  have h := hc (g * x * g⁻¹) hx
  calc x * (g⁻¹ * c * g) = g⁻¹ * ((g * x * g⁻¹) * c) * g := by group
    _ = g⁻¹ * (c * (g * x * g⁻¹)) * g := by rw [h]
    _ = (g⁻¹ * c * g) * x := by group
theorem inf_centralizer_eq_of_mul_centralizer {L : Subgroup G} {s c : G}
    (hc : c ∈ centralizer (L : Set G)) :
    L ⊓ centralizer ({s * c} : Set G) = L ⊓ centralizer ({s} : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hxL, hx⟩
    refine ⟨hxL, ?_⟩
    have hc' : x * c = c * x := Subgroup.mem_centralizer_iff.mp hc x hxL
    exact mul_right_cancel (show (x * s) * c = (s * x) * c from by
      calc (x * s) * c = x * (s * c) := by group
        _ = (s * c) * x := hx
        _ = s * (c * x) := by group
        _ = s * (x * c) := by rw [← hc']
        _ = (s * x) * c := by group)
  · rintro ⟨hxL, hx⟩
    refine ⟨hxL, ?_⟩
    have hc' : x * c = c * x := Subgroup.mem_centralizer_iff.mp hc x hxL
    calc x * (s * c) = (x * s) * c := by group
      _ = (s * x) * c := by rw [hx]
      _ = s * (x * c) := by group
      _ = s * (c * x) := by rw [hc']
      _ = (s * c) * x := by group
theorem mem_twoPrimeRes_of_orderOf_two {H : Subgroup G} {u : G} (hu : u ∈ H) (hu2 : orderOf u = 2) :
    u ∈ twoPrimeRes H := by
  rw [twoPrimeRes]
  exact Subgroup.subset_closure ⟨hu, 1, by simpa using hu2⟩
private theorem twoRes_le (H : Subgroup G) : twoRes H ≤ H := by
  rw [twoRes]; exact (Subgroup.closure_le H).mpr fun _ hx => hx.1
private theorem twoPrimeRes_le (H : Subgroup G) : twoPrimeRes H ≤ H := by
  rw [twoPrimeRes]; exact (Subgroup.closure_le H).mpr fun _ hx => hx.1
theorem xout_le (L : Subgroup G) (s : G) : XOut L s ≤ L ⊓ centralizer ({s} : Set G) := by
  rw [XOut]
  exact (twoPrimeRes_le _).trans (twoRes_le _)
theorem exists_conj_le_of_isSylow2Of [Finite G] {S H K : Subgroup G} (hS : IsSylow2Of S H)
    (hK : IsPGroup 2 K) (hKH : K ≤ H) : ∃ c ∈ H, ∀ k ∈ K, c * k * c⁻¹ ∈ S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hS.exists_sylow
  have hK' : IsPGroup 2 (K.subgroupOf H) :=
    hK.of_equiv (Subgroup.subgroupOfEquivOfLe hKH).symm
  obtain ⟨Q, hKQ⟩ := hK'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (M := ↥H) P Q
  have hcQ : (Q : Subgroup ↥H) = (P : Subgroup ↥H).map (MulAut.conj c).toMonoidHom := by
    rw [← hc, Sylow.coe_subgroup_smul]
    rfl
  refine ⟨(c : G)⁻¹, inv_mem c.2, ?_⟩
  intro k hk
  have hkQ : (⟨k, hKH hk⟩ : ↥H) ∈ (P : Subgroup ↥H).map (MulAut.conj c).toMonoidHom := by
    rw [← hcQ]
    exact hKQ ((Subgroup.mem_subgroupOf).mpr hk)
  obtain ⟨s, hsP, hsk⟩ := Subgroup.mem_map.mp hkQ
  have h2 : (c : G) * (H.subtype s) * (c : G)⁻¹ = k := by
    have h3 := congrArg (fun x : ↥H => (x : G)) hsk
    simpa [MulAut.conj_apply, mul_assoc] using h3
  have hs_eq : H.subtype s = (c : G)⁻¹ * k * c := by
    rw [← h2]
    group
  have hS_eq : (P : Subgroup ↥H).map H.subtype = S := hP
  have hmemS : H.subtype s ∈ S := by
    rw [← hS_eq]
    exact Subgroup.mem_map_of_mem H.subtype hsP
  rw [inv_inv, ← hs_eq]
  exact hmemS
private theorem simple_oddCore_of_lieModel_aux [Finite G] {X : Subgroup G}
    {tag : CFSG.Open.StatedLieTag} {n f : ℕ} (hn : n ≠ 0)
    (hm : LieModel (X ⧸ CFSG.oddCore X) tag n 3 f) :
    IsSimpleGroup (X ⧸ CFSG.oddCore X) :=
  (CFSG.LieType.Simplicity.fam_classical_converse (X ⧸ CFSG.oddCore X)
    ⟨tag, n, 3, f, hm.statedClassicalModel_of_ne_zero hn⟩).2.2
theorem ne_bot_of_shape [Finite G] {X : Subgroup G}
    (h : IsOmega5 X ∨ IsL29 X ∨ IsU33 X ∨ IsL3Eps3 X) : X ≠ ⊥ := by
  intro hbot
  haveI : Subsingleton (X ⧸ oddCore X) := by
    rw [hbot]
    refine QuotientGroup.subsingleton_iff.mpr (le_antisymm le_top fun x _ => ?_)
    have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.mp x.2)
    rw [hx]
    exact Subgroup.one_mem _
  have hsimple : IsSimpleGroup (X ⧸ oddCore X) := by
    rcases h with h | h | h | (h | h) <;>
      exact simple_oddCore_of_lieModel_aux (by norm_num) h
  haveI : Nontrivial (X ⧸ oddCore X) := hsimple.toNontrivial
  obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (X ⧸ oddCore X)).exists_pair_ne
  exact hab (Subsingleton.elim a b)
private theorem two_dvd_card_of_isQuasisimple_aux {X : Type*} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) : 2 ∣ Nat.card X := by
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2.1
  have heven : Even (Nat.card (X ⧸ Subgroup.center X)) :=
    CFSG.Walter.even_card_of_isSimpleGroup hX.2.2
  exact (even_iff_two_dvd.mp heven).trans (Subgroup.card_quotient_dvd_card (Subgroup.center X))
theorem exists_involution_of_isComponentIn [Finite G] {X H : Subgroup G} (h : IsComponentIn X H) :
    ∃ u ∈ X, orderOf u = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card ↥X := two_dvd_card_of_isQuasisimple_aux h.isQuasisimple
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 h2
  exact ⟨(u : G), u.2, by rw [Subgroup.orderOf_coe, hu]⟩
theorem sec7_involution_types [Finite G] (hP : Asc82Tab6P) {L : Subgroup G} (hL : IsOm6P L)
    {u : G} (hu : u ∈ L) (hu2 : orderOf u = 2) :
    InducesTypeSome L u 6 1 4 1 ∨ InducesTypeSome L u 6 1 2 (-1) := by
  have hN : u ∈ normalizer (L : Set G) := Subgroup.le_normalizer hu
  have hinner : InnerOn L u := Subgroup.mem_sup_left hu
  have hnot : u ∉ centralizer (L : Set G) := by
    intro huC
    have huZ : u ∈ centerIn L :=
      Subgroup.mem_map.mpr ⟨⟨u, hu⟩,
        Subgroup.mem_center_iff.mpr fun y =>
          Subtype.ext (Subgroup.mem_centralizer_iff.mp huC y y.2), rfl⟩
    have hu1 : u = 1 := Subgroup.mem_bot.mp (hP.center_triv G L hL ▸ huZ)
    rw [hu1, orderOf_one] at hu2
    norm_num at hu2
  exact (hP.inner_iff G L hL u hu2 hN).mp ⟨hinner, hnot⟩
theorem sec7_z_type [Finite G] (hF : Asc82AutFacts) {t : G} {L S : Subgroup G} {z : G}
    (hc : Sec7Ctx G t L S z) : orderOf z = 2 ∧ InducesTypeSome L z 6 1 4 1 :=
  (hF.pocket_P G L hc.isOm6P z hc.z_mem_L).mp hc.pocket
theorem sec7_not_isConj_z [Finite G] (h73 : Asc82Lemma73) (hP : Asc82Tab6P) {t : G}
    {L S : Subgroup G} {z : G} (hc : Sec7Ctx G t L S z) : ¬ IsConj t z := by
  intro hcon
  obtain ⟨g, hg⟩ := isConj_iff_inv_mul.mp (isConj_comm.mp hcon)
  have hw := h73 G t L S z hc g
    (by rw [hg]; exact Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hdisj : InducesTypeSome L t 6 1 4 1 ∨ InducesTypeSome L t 6 1 2 (-1) ∨
      (∃ α : ℤˣ, InducesTypeSome L t 6 1 1 α) ∨ (∃ α : ℤˣ, InducesTypeSome L t 6 1 3 α) ∨
      InducesOutsideGStar L 6 1 t := by
    rw [hg] at hw
    rcases hw with h3 | h4
    · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
    · exact Or.inl h4
  have hN : t ∈ normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer (L : Set G) hc.t_mem_centralizer
  exact (hP.nontrivial G L hc.isOm6P t hc.involution hN hdisj) hc.t_mem_centralizer
theorem sec7_lemma73_sym [Finite G] (h73 : Asc82Lemma73) {t : G} {L S : Subgroup G} {z : G}
    (hc : Sec7Ctx G t L S z) (g : G) {w : G} (hw : IsConj z w)
    (hwC : w ∈ centralizer ({g⁻¹ * t * g} : Set G)) :
    (∃ α : ℤˣ, InducesTypeSome (CFSG.conjugate L g) w 6 1 3 α) ∨
      InducesTypeSome (CFSG.conjugate L g) w 6 1 4 1 := by
  obtain ⟨c, hc_eq⟩ := isConj_iff.mp hw
  have hh : (g⁻¹ * c⁻¹)⁻¹ * (g⁻¹ * z * g) * (g⁻¹ * c⁻¹) = w := by
    rw [← hc_eq]
    group
  have hmem : (g⁻¹ * c⁻¹)⁻¹ * (g⁻¹ * z * g) * (g⁻¹ * c⁻¹) ∈
      centralizer ({g⁻¹ * t * g} : Set G) := by
    rw [hh]
    exact hwC
  have hres := h73 G (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g) (g⁻¹ * z * g)
    (hc.conjugate g) (g⁻¹ * c⁻¹) hmem
  rw [hh] at hres
  exact hres
theorem Sec7Ctx.nonabelian [Finite G] {t : G} {L S : Subgroup G} {z : G}
    (hc : Sec7Ctx G t L S z) : ∃ a b : G, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hcenter : Subgroup.center ↥L = ⊤ := by
    refine le_antisymm le_top fun x _ => ?_
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (h y x)
  haveI : Subsingleton (↥L ⧸ Subgroup.center ↥L) := by
    rw [QuotientGroup.subsingleton_iff]
    exact hcenter
  haveI : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hc.component.isQuasisimple.2.1.toNontrivial
  obtain ⟨a, b, hab⟩ :=
    (inferInstance : Nontrivial (↥L ⧸ Subgroup.center ↥L)).exists_pair_ne
  exact hab (Subsingleton.elim a b)
private theorem exists_conj_commute_ne_aux [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2) :
    ∃ g : G, g * z * g⁻¹ * z = z * (g * z * g⁻¹) ∧ g * z * g⁻¹ ≠ z := by
  have : Fintype G := Fintype.ofFinite G
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  have hzz : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  by_contra hcon
  push Not at hcon
  obtain ⟨K, hKn, hKodd, hK⟩ := CFSG.ZStar.glauberman_zStar G z hz1 hzz hcon
  rcases Subgroup.Normal.eq_bot_or_eq_top K with hbot | htop
  · have hcent : z ∈ center G := mem_center_iff.mpr fun g => by
      have h := hK g
      rw [hbot, mem_bot, mul_inv_eq_one] at h
      calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h]
    have hc : center G = ⊥ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top (center G) with h | h
      · exact h
      · obtain ⟨a, b, hab⟩ := hnab
        exact absurd (mem_center_iff.mp (h ▸ mem_top a) b).symm hab
    rw [hc, mem_bot] at hcent
    exact hz1 hcent
  · rw [htop, card_top] at hKodd
    have h2 : 2 ∣ Nat.card G := hz ▸ _root_.orderOf_dvd_natCard z
    exact (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr h2)
theorem sec7_zstar [Finite G] (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) {t : G}
    (ht : orderOf t = 2) :
    ∃ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) ∧ g⁻¹ * t * g ≠ t := by
  haveI := hs
  obtain ⟨g, hg1, hg2⟩ := exists_conj_commute_ne_aux hnab ht
  refine ⟨g⁻¹, ?_, ?_⟩
  · rw [inv_inv]; exact Subgroup.mem_centralizer_singleton_iff.mpr hg1
  · rw [inv_inv]; exact hg2
theorem sec7_not_central [Finite G] (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) {t : G}
    {L S : Subgroup G} {z : G} (hc : Sec7Ctx G t L S z) {s : G} (hs2 : orderOf s = 2)
    (hsC : s ∈ centralizer ({t} : Set G)) (hst : s ≠ t) :
    s ∈ normalizer (L : Set G) ∧ s ∉ centralizer (L : Set G) := by
  refine ⟨hc.cent_le_normalizer h36 s hsC, ?_⟩
  intro hsL
  have hs1 : s * s = 1 := by rw [← pow_two, ← hs2, pow_orderOf_eq_one]
  have hst_comm : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.mp hsC
  have hcyc := h72 G t L hc.toSec3SettingLB hc.omega6
  rcases eq_one_or_eq_of_commute hcyc hsL hc.t_mem_centralizer hs1 hc.involution hst_comm with
    h | h
  · rw [h, orderOf_one] at hs2; norm_num at hs2
  · exact hst h
theorem sec7_inner_decomp [Finite G] (h72 : Asc82Lemma72) (hP : Asc82Tab6P) {t : G}
    {L S : Subgroup G} {z : G} (hc : Sec7Ctx G t L S z) {s : G} (hs2 : orderOf s = 2)
    (hsC : s ∈ centralizer ({t} : Set G)) (hst : s ≠ t) (hin : InnerOn L s) :
    ∃ v ∈ L, ∃ c ∈ centralizer (L : Set G), orderOf v = 2 ∧ (c = 1 ∨ c = t) ∧ s = v * c := by
  obtain ⟨l, hlL, c, hcC, hslc⟩ := innerOn_decompose hin
  have hcl : c * l = l * c := (Subgroup.mem_centralizer_iff.mp hcC l hlL).symm
  have hs1 : s * s = 1 := by rw [← pow_two, ← hs2, pow_orderOf_eq_one]
  have hmul : (l * c) * (l * c) = (l * l) * (c * c) := by
    calc (l * c) * (l * c) = l * (c * l) * c := by group
      _ = l * (l * c) * c := by rw [hcl]
      _ = (l * l) * (c * c) := by group
  have h1 : (l * l) * (c * c) = 1 := by rw [← hmul, ← hslc, hs1]
  have hll_eq : l * l = (c * c)⁻¹ := mul_eq_one_iff_eq_inv.mp h1
  have hinf : L ⊓ centralizer (L : Set G) ≤ centerIn L := fun x hx =>
    Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩,
      Subgroup.mem_center_iff.mpr fun y =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 y y.2), rfl⟩
  have hl1 : l * l = 1 := by
    have hZ := hinf ⟨mul_mem hlL hlL, by
      rw [hll_eq]; exact (centralizer (L : Set G)).inv_mem (mul_mem hcC hcC)⟩
    exact Subgroup.mem_bot.mp (hP.center_triv G L hc.isOm6P ▸ hZ)
  have hc1 : c * c = 1 := by rw [hl1, one_mul] at h1; exact h1
  have hc_mem_ct : c ∈ centralizer ({t} : Set G) := by
    have hceq : c = l⁻¹ * s := by rw [hslc]; group
    rw [hceq]
    exact mul_mem (inv_mem (hc.le_centralizer hlL)) hsC
  have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hc_mem_ct
  have hcyc := h72 G t L hc.toSec3SettingLB hc.omega6
  have hct' : c = 1 ∨ c = t :=
    eq_one_or_eq_of_commute hcyc hcC hc.t_mem_centralizer hc1 hc.involution hct
  have hl_ne : l ≠ 1 := by
    intro hl
    rw [hl, one_mul] at hslc
    rcases hct' with hc_eq | hc_eq
    · rw [hc_eq] at hslc; rw [hslc, orderOf_one] at hs2; norm_num at hs2
    · exact hst (hslc.trans hc_eq)
  have hl2 : orderOf l = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (p := 2) (by rwa [pow_two]) hl_ne
  exact ⟨l, hlL, c, hcC, hl2, hct', hslc⟩

end CFSG.OddStandard.SmallF3.Omega
