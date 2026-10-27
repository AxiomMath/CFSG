module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XHyp
import CFSG.GroupTheory.ElemAbelianRank
import CFSG.HardMathSupport.Timmesfeld.Proving.TwoLocalAttain
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XRank
import CFSG.GroupTheory.SupCommute
import TauCeti.GroupTheory.PGroup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Trans
import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω} {G₀ : Type} [Group G₀]

private lemma eq_zpowers_sup_inf_aux1 {p : ℕ} {S : Subgroup Ω} (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) {s : ↥S} (hs : s ^ p ∈ Subgroup.center ↥S) :
    ∃ t ∈ Subgroup.center ↥S, (s * t⁻¹) ^ p = 1 := by
  have hkdvd : orderOf (s ^ p) ∣ Nat.card (Subgroup.center ↥S) :=
    Subgroup.orderOf_dvd_natCard _ hs
  have hk0 : orderOf (s ^ p) ≠ 0 := (orderOf_pos _).ne'
  have hcop : p.Coprime (orderOf (s ^ p)) :=
    hp.coprime_iff_not_dvd.mpr fun hd => hZ (hd.trans hkdvd)
  obtain ⟨m, -, hmod⟩ :=
    Nat.exists_mul_mod_eq_of_coprime (k := orderOf (s ^ p)) (n := p) 1 hcop hk0
  have hzpow : (s ^ p) ^ (p * m) = s ^ p := by
    have h1 := (pow_eq_pow_iff_modEq (x := s ^ p) (n := p * m) (m := 1)).2 hmod
    simpa using h1
  refine ⟨(s ^ p) ^ m, Subgroup.pow_mem _ hs m, ?_⟩
  have hsz : Commute s (s ^ p) := (Commute.refl s).pow_right p
  have ht : Commute s ((s ^ p) ^ m) := hsz.pow_right m
  have htp : ((s ^ p) ^ m) ^ p = s ^ p := by
    rw [← pow_mul, mul_comm m p]; exact hzpow
  rw [(ht.inv_right).mul_pow p, inv_pow, htp, mul_inv_cancel]

private lemma eq_zpowers_sup_inf_aux3 {p : ℕ} {S : Subgroup Ω} {s : ↥S} {c : Ω}
    (hc : c ∈ Subgroup.centralizer (S : Set Ω)) (hsp_cp : (s : Ω) ^ p * c ^ p = 1)
    (hp : p.Prime) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) :
    ∃ t ∈ Subgroup.center ↥S, (t : Ω) ∈ Subgroup.centralizer (S : Set Ω) ∧ ((t : Ω) * c) ^ p = 1 := by
  have hzj : s ^ p ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have h1 : (s : Ω) ^ p = (c ^ p)⁻¹ := mul_eq_one_iff_eq_inv.1 hsp_cp
    have h2 : (c ^ p)⁻¹ ∈ Subgroup.centralizer (S : Set Ω) :=
      Subgroup.inv_mem _ (Subgroup.pow_mem _ hc p)
    calc (y : Ω) * ((s ^ p : ↥S) : Ω) = (y : Ω) * (s : Ω) ^ p := by rw [Subgroup.coe_pow]
      _ = (y : Ω) * (c ^ p)⁻¹ := by rw [h1]
      _ = (c ^ p)⁻¹ * (y : Ω) := Subgroup.mem_centralizer_iff.1 h2 (y : Ω) y.2
      _ = ((s ^ p : ↥S) : Ω) * (y : Ω) := by rw [Subgroup.coe_pow, h1]
  obtain ⟨t, ht, htp⟩ := eq_zpowers_sup_inf_aux1 hp hZ hzj
  have htcent : (t : Ω) ∈ Subgroup.centralizer (S : Set Ω) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 ht ⟨y, hy⟩)
  have hst : Commute s t := Subgroup.mem_center_iff.1 ht s
  have hstp' : t ^ p = s ^ p := by
    have h1 : s ^ p * (t⁻¹) ^ p = 1 := by
      rw [← (hst.inv_right).mul_pow p]; exact htp
    have h2 : s ^ p * (t ^ p)⁻¹ = 1 := by simpa [inv_pow] using h1
    have h3 : s ^ p = t ^ p := by
      have := mul_eq_one_iff_eq_inv.1 h2
      simpa using this
    exact h3.symm
  have hstp : (t : Ω) ^ p = (s : Ω) ^ p := by
    calc (t : Ω) ^ p = ((t ^ p : ↥S) : Ω) := (map_pow (Subgroup.subtype S) t p).symm
      _ = ((s ^ p : ↥S) : Ω) := by rw [hstp']
      _ = (s : Ω) ^ p := map_pow (Subgroup.subtype S) s p
  have htc : Commute (t : Ω) c := Subgroup.mem_centralizer_iff.1 hc (t : Ω) t.2
  refine ⟨t, ht, htcent, ?_⟩
  rw [htc.mul_pow p, hstp]
  exact hsp_cp

private lemma eq_zpowers_sup_inf_aux2 (hcfg : Cfg173 p S B N D K x) (M : S172X.S172Model S B G₀)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) {b : Ω} (hb : b ∈ B) :
    ∃ a c' : Ω, a ∈ S ∧ c' ∈ Subgroup.centralizer (S : Set Ω) ∧ c' ^ p = 1 ∧
      Commute x c' ∧ b = a * c' := by
  obtain ⟨s, c, hc, hb_eq, -⟩ := M.split ⟨b, hb⟩
  have hsc : Commute (s : Ω) c := Subgroup.mem_centralizer_iff.1 hc (s : Ω) s.2
  have hbp : (b : Ω) ^ p = 1 := hcfg.elem.2 b hb
  have hsp_cp : (s : Ω) ^ p * c ^ p = 1 := by
    rw [← hsc.mul_pow p, ← hb_eq]
    exact hbp
  obtain ⟨t, ht, htcent, hc'p⟩ := eq_zpowers_sup_inf_aux3 hc hsp_cp hcfg.prime hZ
  have hxcent : x ∈ Subgroup.centralizer (S : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  have hxsp : Commute x ((s * t⁻¹ : ↥S) : Ω) := by
    have h := Subgroup.mem_centralizer_iff.1 hxcent ((s * t⁻¹ : ↥S) : Ω) (s * t⁻¹).2
    exact h.symm
  have hxb : Commute x b := hcfg.elem.comm hcfg.mem hb
  have hb' : b = (s : Ω) * c := hb_eq
  have hbc' : b = ((s * t⁻¹ : ↥S) : Ω) * ((t : Ω) * c) := by
    rw [hb']
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hc'comm : Commute x ((t : Ω) * c) := by
    have hce : (t : Ω) * c = (((s * t⁻¹ : ↥S) : Ω))⁻¹ * b := by
      rw [hbc']; group
    rw [hce]
    exact (hxsp.inv_right).mul_right hxb
  exact ⟨((s * t⁻¹ : ↥S) : Ω), (t : Ω) * c, (s * t⁻¹).2,
    Subgroup.mul_mem _ htcent hc, hc'p, hc'comm, hbc'⟩

private lemma eq_zpowers_sup_inf_aux4 (hcfg : Cfg173 p S B N D K x) {c' : Ω}
    (hc'cent : c' ∈ Subgroup.centralizer (S : Set Ω)) (hc'p : c' ^ p = 1) (hxc' : Commute x c') :
    c' ∈ Subgroup.zpowers x := by
  have hxcent : x ∈ Subgroup.centralizer (S : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  let D : Subgroup Ω := Subgroup.zpowers x ⊔ Subgroup.zpowers c'
  have hxel : CFSG.Open.IsElemAbelian p (Subgroup.zpowers x) :=
    CFSG.Open.isElemAbelian_zpowers (hcfg.elem.2 x hcfg.mem)
  have hc'el : CFSG.Open.IsElemAbelian p (Subgroup.zpowers c') :=
    CFSG.Open.isElemAbelian_zpowers hc'p
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers c', a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (hxc'.zpow_zpow m n).eq
  have hDab : CFSG.Open.IsElemAbelian p D :=
    CFSG.Open.IsElemAbelian.sup_of_commute hxel hc'el hcomm
  have hDp : IsPGroup p D := isPGroup_of_isElemAbelian hDab
  have hDle : D ≤ Subgroup.centralizer (S : Set Ω) :=
    sup_le (Subgroup.zpowers_le.2 hxcent) (Subgroup.zpowers_le.2 hc'cent)
  have hcm : ∀ g ∈ D, CentMod p S g := fun g hg =>
    CFSG.LocalAnalysis.GLTheoremA.centMod_of_mem_centralizer (hDle hg)
  have hcyc : IsCyclic D := hcfg.cyc D hcm hDp
  have hcard : Nat.card D ≤ p :=
    card_le_of_isCyclic_of_pow hcfg.prime hcyc hDab.2
  exact mem_zpowers_of_card_sup_le hcfg.prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one hcard

theorem eq_zpowers_sup_inf (hcfg : Cfg173 p S B N D K x) (M : S172X.S172Model S B G₀)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) : B = Subgroup.zpowers x ⊔ B ⊓ S := by
  apply le_antisymm
  · intro b hb
    obtain ⟨a, c', haS, hc'cent, hc'p, hxc', hb_ac'⟩ := eq_zpowers_sup_inf_aux2 hcfg M hZ hb
    have hc'zp : c' ∈ Subgroup.zpowers x := eq_zpowers_sup_inf_aux4 hcfg hc'cent hc'p hxc'
    have hc'B : c' ∈ B := Subgroup.zpowers_le.2 hcfg.mem hc'zp
    have haB : a ∈ B := by
      have h : a = b * c'⁻¹ := by rw [hb_ac']; group
      rw [h]; exact Subgroup.mul_mem _ hb (Subgroup.inv_mem _ hc'B)
    have hmem : a * c' ∈ (B ⊓ S) ⊔ Subgroup.zpowers x :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨haB, haS⟩) (Subgroup.mem_sup_right hc'zp)
    rw [hb_ac']
    rwa [sup_comm]
  · exact sup_le (Subgroup.zpowers_le.2 hcfg.mem) inf_le_left

theorem card_eq_mul_card_range (hcfg : Cfg173 p S B N D K x) (M : S172X.S172Model S B G₀) :
    Nat.card B = p * Nat.card M.β.range := by
  haveI : Fact p.Prime := ⟨hcfg.prime⟩
  have hker : M.β.ker = (Subgroup.zpowers x).subgroupOf B := by
    rw [M.ker_β]
    ext b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hcfg.cent (b : Ω) b.2
  have hcardker : Nat.card M.β.ker = p := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 hcfg.mem)).toEquiv,
      Nat.card_zpowers, orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one]
  have hmul := Subgroup.card_ker_mul_card_range M.β
  rw [← hmul, hcardker]

theorem card_range_le [Finite G₀] (hcfg : Cfg173 p S B N D K x) (M : S172X.S172Model S B G₀) :
    Nat.card M.β.range ≤ p ^ GLATwoLocalRank p G₀ := by
  have hp := hcfg.prime
  have hĀ : IsElemAbelian p M.β.range := M.isElemAbelian_range_β hcfg.elem
  obtain ⟨T', hT'1, hT'2, hT'N⟩ := exists_two_subgroup_of_hb hcfg M
  have hle : CFSG.Open.pRank p M.β.range ≤ GLATwoLocalRank p G₀ :=
    (CFSG.SectionRank.pRank_mono hp.one_lt hT'N).trans
      (pRank_normalizer_le hp.one_lt hT'1 hT'2)
  rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hĀ]
  exact Nat.pow_le_pow_right hp.pos hle

private theorem exists_pLift_aux1 {R : Type*} [Group R] {p : ℕ} (hp : p.Prime)
    {Z Q : Subgroup R} (hZ : ¬ p ∣ Nat.card Z) (hZc : Z ≤ Subgroup.center R)
    (hQp : IsPGroup p Q) {x : R} (hx : ∃ k, x ^ p ^ k = 1)
    (hxZ : ∃ z ∈ Z, ∃ q ∈ Q, z * q = x) : x ∈ Q := by
  obtain ⟨z, hz, q, hq, rfl⟩ := hxZ
  haveI : Z.Normal := Subgroup.normal_of_le_center hZc
  have hZr : Nat.Coprime (Nat.card Z) p := (hp.coprime_iff_not_dvd.mpr hZ).symm
  obtain ⟨k, hk⟩ := hx
  have hz1 : QuotientGroup.mk' Z z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
  have hmem : QuotientGroup.mk' Z (z * q) ∈ Q.map (QuotientGroup.mk' Z) := by
    rw [map_mul, hz1, one_mul]
    exact Subgroup.mem_map_of_mem _ hq
  exact CFSG.LieType.BorelTits.mem_of_mk_mem_map Z hZc hZr hQp hmem hk

private theorem exists_pLift_aux2 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    {G₀ : Type} [Group G₀] (M : S172X.S172Model S B G₀) {E : Subgroup G₀}
    (hE : IsElemAbelian p E) (hp : p.Prime) :
    ∃ (R : Subgroup ↥S) (πR : ↥R →* E) (Q : Sylow p ↥R),
      R = E.comap M.π ∧ ((Q : Subgroup ↥R).map πR : Subgroup E) = ⊤ ∧
      (∀ r, (πR r : G₀) = M.π (r : ↥S)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let R : Subgroup ↥S := E.comap M.π
  have hRmap : R.map M.π = E := Subgroup.map_comap_eq_self_of_surjective M.surj E
  let πR : ↥R →* E :=
    { toFun := fun r => ⟨M.π (r : ↥S), Subgroup.mem_comap.1 r.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hπR_surj : Function.Surjective πR := by
    intro e
    have he : (e : G₀) ∈ R.map M.π := by rw [hRmap]; exact e.2
    obtain ⟨s, hsR, hse⟩ := Subgroup.mem_map.1 he
    exact ⟨⟨s, hsR⟩, Subtype.ext hse⟩
  let Q : Sylow p ↥R := default
  let Qmap : Sylow p E := Q.mapSurjective hπR_surj
  have hEisp : IsPGroup p E := isPGroup_of_isElemAbelian hE
  have hQmap_top : (Qmap : Subgroup E) = ⊤ :=
    (Qmap.is_maximal' (Q := (⊤ : Subgroup E)) (hEisp.to_subgroup ⊤) le_top).symm
  exact ⟨R, πR, Q, rfl, by simpa [Qmap] using hQmap_top, fun r => rfl⟩

private theorem exists_pLift_aux6 {Ω : Type} [Group Ω] {S B : Subgroup Ω}
    {G₀ : Type} [Group G₀] (M : S172X.S172Model S B G₀) {E : Subgroup G₀}
    {R : Subgroup ↥S} (πR : ↥R →* E)
    (hπRval : ∀ r, (πR r : G₀) = M.π (r : ↥S)) :
    πR.ker = (Subgroup.center ↥S).subgroupOf R := by
  ext r
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h' : M.π (r : ↥S) = 1 := by
      have h0 := congrArg (fun z : E => (z : G₀)) h
      rwa [hπRval r] at h0
    rw [← M.ker_π, MonoidHom.mem_ker]
    exact h'
  · intro h
    rw [← M.ker_π, MonoidHom.mem_ker] at h
    apply Subtype.ext
    rw [hπRval r]
    exact h

private theorem exists_pLift_aux7 {p : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω}
    {G₀ : Type} [Group G₀] {E : Subgroup G₀} {R : Subgroup ↥S} {Q : Subgroup ↥R}
    (hE : IsElemAbelian p E) (f : ↥Q →* G₀) (hf_inj : Function.Injective f)
    (hle : ∀ x, f x ∈ E) : IsElemAbelian p Q := by
  have htop : E.comap f = ⊤ := by
    ext x
    simpa [Subgroup.mem_comap] using hle x
  have hcom : IsElemAbelian p (⊤ : Subgroup ↥Q) := by
    simpa [htop] using hE.comap hf_inj
  have hmap := CFSG.SectionRank.isElemAbelian_map hcom Q.subtype
  have htopmap : (⊤ : Subgroup ↥Q).map Q.subtype = Q := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  rwa [htopmap] at hmap

private lemma not_dvd_card_center_subgroupOf {p : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) (R : Subgroup ↥S) :
    ¬ p ∣ Nat.card ((Subgroup.center ↥S).subgroupOf R) := by
  have hcard : Nat.card ((Subgroup.center ↥S).subgroupOf R) =
      Nat.card (Subgroup.center ↥S ⊓ R : Subgroup ↥S) := by
    rw [← Subgroup.inf_subgroupOf_right (Subgroup.center ↥S) R]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  intro hd
  exact hZ (hd.trans (hcard ▸ Subgroup.card_dvd_of_le inf_le_left))

private lemma not_dvd_card_center_map {p : ℕ} {Ω : Type} [Group Ω] {S : Subgroup Ω}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) :
    ¬ p ∣ Nat.card ((Subgroup.center ↥S).map S.subtype) := by
  rwa [Subgroup.card_map_of_injective S.subtype_injective]

private theorem exists_pLift_aux3 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    {G₀ : Type} [Group G₀] {N D K : Subgroup Ω} {x : Ω} (hcfg : Cfg173 p S B N D K x)
    (M : S172X.S172Model S B G₀) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) {E : Subgroup G₀}
    (hE : IsElemAbelian p E) {R : Subgroup ↥S} (πR : ↥R →* E) (Q : Sylow p ↥R)
    (hQmap_coe : ((Q : Subgroup ↥R).map πR : Subgroup E) = ⊤)
    (hπRval : ∀ r, (πR r : G₀) = M.π (r : ↥S)) :
    Nat.card ↥(Q : Subgroup ↥R) = Nat.card E ∧ IsElemAbelian p (Q : Subgroup ↥R) ∧
      πR.ker = (Subgroup.center ↥S).subgroupOf R ∧
      Disjoint (Q : Subgroup ↥R) ((Subgroup.center ↥S).subgroupOf R) ∧
      (πR.comp (Q : Subgroup ↥R).subtype).range = ⊤ := by
  have hp := hcfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  let f : ↥Q →* E := πR.comp (Q : Subgroup ↥R).subtype
  have hf_range : f.range = ⊤ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hQmap_coe
  have hker := exists_pLift_aux6 M πR hπRval
  have hZR : ¬ p ∣ Nat.card ((Subgroup.center ↥S).subgroupOf R) :=
    not_dvd_card_center_subgroupOf hZ R
  have hQZ : Disjoint (Q : Subgroup ↥R) ((Subgroup.center ↥S).subgroupOf R) :=
    (TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup
      (C := (Subgroup.center ↥S).subgroupOf R) (Q := (Q : Subgroup ↥R)) hZR Q.isPGroup').symm
  have hf_inj : Function.Injective f := by
    intro a b hab
    have hmem : ((a⁻¹ * b : ↥Q) : ↥R) ∈ (Q : Subgroup ↥R) ⊓ πR.ker := by
      refine Subgroup.mem_inf.2 ⟨(a⁻¹ * b : ↥Q).2, ?_⟩
      rw [MonoidHom.mem_ker]
      exact (by rw [map_mul, map_inv, hab, inv_mul_cancel] : f (a⁻¹ * b) = 1)
    rw [hker] at hmem
    have h1 := Subgroup.disjoint_def.1 hQZ (Subgroup.mem_inf.1 hmem).1 (Subgroup.mem_inf.1 hmem).2
    exact inv_mul_eq_one.1 (Subtype.ext h1)
  have hf_surj : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top]
    exact hf_range
  have hQcard : Nat.card ↥(Q : Subgroup ↥R) = Nat.card ↥E :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  have hQel : IsElemAbelian p (Q : Subgroup ↥R) :=
    exists_pLift_aux7 hE (E.subtype.comp f) (E.subtype_injective.comp hf_inj)
      (fun x => (f x).2)
  exact ⟨hQcard, hQel, hker, hQZ, hf_range⟩

private theorem exists_pLift_aux4 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    {G₀ : Type} [Group G₀] (M : S172X.S172Model S B G₀) {E : Subgroup G₀}
    {R : Subgroup ↥S} (πR : ↥R →* E) (Q : Sylow p ↥R)
    (hQmap_coe : ((Q : Subgroup ↥R).map πR : Subgroup E) = ⊤)
    (hQcard : Nat.card ↥(Q : Subgroup ↥R) = Nat.card E)
    (hQel : IsElemAbelian p (Q : Subgroup ↥R))
    (hπRval : ∀ r, (πR r : G₀) = M.π (r : ↥S)) :
    ∃ P : Subgroup Ω, P ≤ S ∧ IsElemAbelian p P ∧ piImg M P = E ∧ Nat.card P = Nat.card E ∧
      P = ((Q : Subgroup ↥R).map R.subtype).map S.subtype := by
  let P : Subgroup Ω := ((Q : Subgroup ↥R).map R.subtype).map S.subtype
  have hPleS : P ≤ S := Subgroup.map_subtype_le _
  have hPcard : Nat.card P = Nat.card E := by
    change Nat.card (((Q : Subgroup ↥R).map R.subtype).map S.subtype) = Nat.card E
    rw [Subgroup.card_map_of_injective S.subtype_injective,
      Subgroup.card_map_of_injective R.subtype_injective, hQcard]
  have hP_el : IsElemAbelian p P := by
    change IsElemAbelian p (((Q : Subgroup ↥R).map R.subtype).map S.subtype)
    exact CFSG.SectionRank.isElemAbelian_map
      (CFSG.SectionRank.isElemAbelian_map hQel R.subtype) S.subtype
  have hPs : P.subgroupOf S = (Q : Subgroup ↥R).map R.subtype := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hPleS]
  have hpiP : piImg M P = E := by
    rw [piImg, hPs, Subgroup.map_map]
    have hhom : M.π.comp R.subtype = E.subtype.comp πR :=
      MonoidHom.ext fun r => (hπRval r).symm
    rw [hhom, ← Subgroup.map_map, hQmap_coe]
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  exact ⟨P, hPleS, hP_el, hpiP, hPcard, rfl⟩

private theorem exists_pLift_aux8 {Ω : Type} [Group Ω] {S B : Subgroup Ω}
    {G₀ : Type} [Group G₀] (M : S172X.S172Model S B G₀)
    {R : Subgroup ↥S} :
    (Subgroup.center ↥S).subgroupOf R ≤ Subgroup.center ↥R := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.1 (Subgroup.mem_subgroupOf.1 hz) (y : ↥S)

private theorem exists_pLift_aux9 {p : ℕ} {Ω : Type} [Group Ω] {S B : Subgroup Ω}
    {G₀ : Type} [Group G₀] (M : S172X.S172Model S B G₀) (hp : p.Prime)
    {E : Subgroup G₀} {R : Subgroup ↥S} (πR : ↥R →* E) (Q : Sylow p ↥R)
    (hker : πR.ker = (Subgroup.center ↥S).subgroupOf R)
    (hf_range : (πR.comp (Q : Subgroup ↥R).subtype).range = ⊤)
    (hZR : ¬ p ∣ Nat.card ((Subgroup.center ↥S).subgroupOf R))
    (hZRc : (Subgroup.center ↥S).subgroupOf R ≤ Subgroup.center ↥R)
    (Q₁R : Subgroup ↥R) (hQ₁Rp : IsPGroup p Q₁R) : Q₁R ≤ (Q : Subgroup ↥R) := by
  intro x hx
  have hxp : ∃ k, x ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := hQ₁Rp ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hex : πR x ∈ (πR.comp (Q : Subgroup ↥R).subtype).range := by
    rw [hf_range]
    exact Subgroup.mem_top _
  obtain ⟨q, hq⟩ := MonoidHom.mem_range.1 hex
  let z : ↥R := x * (q.1 : ↥R)⁻¹
  have hq' : πR ((q : ↥Q) : ↥R) = πR x := hq
  have hzker : z ∈ πR.ker := by
    rw [MonoidHom.mem_ker]
    dsimp [z]
    rw [map_mul, map_inv, ← hq', mul_inv_cancel]
  have hzZ : z ∈ (Subgroup.center ↥S).subgroupOf R := by
    rwa [hker] at hzker
  have hxZ : ∃ z0 ∈ (Subgroup.center ↥S).subgroupOf R,
      ∃ q0 ∈ (Q : Subgroup ↥R), z0 * q0 = x :=
    ⟨z, hzZ, (q.1 : ↥R), q.2, by dsimp [z]; group⟩
  exact exists_pLift_aux1 hp hZR hZRc Q.isPGroup' hxp hxZ

private theorem exists_pLift_aux5 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    {G₀ : Type} [Group G₀] {N D K : Subgroup Ω} {x : Ω} (hcfg : Cfg173 p S B N D K x)
    (M : S172X.S172Model S B G₀) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) {E : Subgroup G₀}
    {R : Subgroup ↥S} (πR : ↥R →* E) (Q : Sylow p ↥R) {P : Subgroup Ω}
    (hPS : P ≤ S) (hP_el : IsElemAbelian p P) (hPpi : piImg M P = E)
    (hPcard : Nat.card P = Nat.card E)
    (hker : πR.ker = (Subgroup.center ↥S).subgroupOf R)
    (hf_range : (πR.comp (Q : Subgroup ↥R).subtype).range = ⊤)
    (hR : R = E.comap M.π)
    (hPdef : P = ((Q : Subgroup ↥R).map R.subtype).map S.subtype) :
    ∀ Q₁ : Subgroup Ω, Q₁ ≤ S → IsPGroup p Q₁ → piImg M Q₁ ≤ E → Q₁ ≤ P := by
  have hp := hcfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  let f : ↥Q →* E := πR.comp (Q : Subgroup ↥R).subtype
  intro Q₁ hQ₁S hQ₁p hQ₁E
  let Q₁S : Subgroup ↥S := Q₁.subgroupOf S
  have hQ₁R : Q₁S ≤ R := by
    rw [hR]
    exact Subgroup.map_le_iff_le_comap.mp (by simpa [piImg, Q₁S] using hQ₁E)
  let Q₁R : Subgroup ↥R := Q₁S.subgroupOf R
  have hQ₁Rp : IsPGroup p Q₁R := (hQ₁p.comap_subtype).comap_subtype
  have hZRc := exists_pLift_aux8 M (R := R)
  have hZR := not_dvd_card_center_subgroupOf hZ R
  have hacc := exists_pLift_aux9 M hcfg.prime πR Q hker hf_range hZR hZRc Q₁R hQ₁Rp
  have hQ₁Sm : Q₁S.map S.subtype = Q₁ := Subgroup.map_subgroupOf_eq_of_le hQ₁S
  have hQ₁Rm : Q₁R.map R.subtype = Q₁S := Subgroup.map_subgroupOf_eq_of_le hQ₁R
  calc Q₁ = Q₁S.map S.subtype := hQ₁Sm.symm
    _ = (Q₁R.map R.subtype).map S.subtype := by rw [hQ₁Rm]
    _ ≤ ((Q : Subgroup ↥R).map R.subtype).map S.subtype :=
        Subgroup.map_mono (Subgroup.map_mono hacc)
    _ = P := hPdef.symm

theorem exists_pLift (hcfg : Cfg173 p S B N D K x) (M : S172X.S172Model S B G₀)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) {E : Subgroup G₀} (hE : IsElemAbelian p E) :
    ∃ P : Subgroup Ω, P ≤ S ∧ IsElemAbelian p P ∧ piImg M P = E ∧ Nat.card P = Nat.card E ∧
      ∀ Q : Subgroup Ω, Q ≤ S → IsPGroup p Q → piImg M Q ≤ E → Q ≤ P := by
  obtain ⟨R, πR, Q, hR, hQmap_coe, hπRval⟩ := exists_pLift_aux2 M hE hcfg.prime
  obtain ⟨hQcard, hQel, hker, hQZ, hf_range⟩ :=
    exists_pLift_aux3 hcfg M hZ hE πR Q hQmap_coe hπRval
  obtain ⟨P, hPS, hP_el, hPpi, hPcard, hPdef⟩ :=
    exists_pLift_aux4 M πR Q hQmap_coe hQcard hQel hπRval
  exact ⟨P, hPS, hP_el, hPpi, hPcard,
    exists_pLift_aux5 hcfg M hZ πR Q hPS hP_el hPpi hPcard hker hf_range hR hPdef⟩
private lemma map_pCore_two_eq_top_of_ker_le_center {V T : Type*} [Group V] [Finite V] [Group T] [Finite T]
    (f : V →* T) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center V) (hT : IsPGroup 2 T) :
    (pCore 2 V).map f = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent T := hT.isNilpotent
  have hnil : Group.IsNilpotent V := isNilpotent_of_ker_le_center f hker
  let Q : Sylow 2 V := default
  have hQn : (Q : Subgroup V).Normal := inferInstance
  have hQeq : (Q : Subgroup V) = pCore 2 V := by
    refine le_antisymm ?_ (IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := 2) (G := V)) Q)
    exact le_sSup ⟨hQn, Q.isPGroup'⟩
  have hQmap : (Q : Subgroup V).map f = ⊤ := by
    have h := (Sylow.mapSurjective hf Q).is_maximal' (Q := (⊤ : Subgroup T)) (hT.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  rw [← hQeq]
  exact hQmap

theorem exists_twoCore_preimage_lift {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    {G₀ : Type} [Group G₀] (M : S172X.S172Model S B G₀) {X : Subgroup Ω} (hXS : X ≤ S)
    {T' : Subgroup G₀} (hT'le : T' ≤ piImg M X) (hT'2 : IsPGroup 2 T') (hT'1 : T' ≠ ⊥) :
    ∃ U : Subgroup Ω, U ≤ X ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ piImg M U = T' ∧
      ∀ s : ↥S, (s : Ω) ∈ Subgroup.normalizer (X : Set Ω) →
        M.π s ∈ Subgroup.normalizer (T' : Set G₀) → (s : Ω) ∈ Subgroup.normalizer (U : Set Ω) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite G₀ := Finite.of_surjective M.π M.surj
  let XS : Subgroup ↥S := X.subgroupOf S
  let TS : Subgroup ↥S := T'.comap M.π
  let V : Subgroup ↥S := XS ⊓ TS
  let g : V →* T' :=
    { toFun := fun v => ⟨M.π (v : ↥S), Subgroup.mem_comap.1 (Subgroup.mem_inf.1 v.2).2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hg_surj : Function.Surjective g := by
    intro t
    have htX : (t : G₀) ∈ XS.map M.π := by
      simpa [XS, piImg] using hT'le t.2
    obtain ⟨x, hxX, hxπ⟩ := Subgroup.mem_map.1 htX
    refine ⟨⟨x, Subgroup.mem_inf.2 ⟨hxX, Subgroup.mem_comap.2 ?_⟩⟩, Subtype.ext hxπ⟩
    rw [hxπ]
    exact t.2
  have hgker : g.ker ≤ Subgroup.center V := by
    intro v hv
    rw [Subgroup.mem_center_iff]
    intro w
    have hvπ : M.π (v : ↥S) = 1 := by
      have h := congrArg (fun z : T' => (z : G₀)) (MonoidHom.mem_ker.1 hv)
      simpa [g] using h
    have hvc : (v : ↥S) ∈ Subgroup.center ↥S := by
      rw [← M.ker_π, MonoidHom.mem_ker]
      exact hvπ
    apply Subtype.ext
    simpa using Subgroup.mem_center_iff.1 hvc (w : ↥S)
  have hpc_map : (pCore 2 V).map g = ⊤ :=
    map_pCore_two_eq_top_of_ker_le_center g hg_surj hgker hT'2
  have hpc_T : (pCore 2 V).map (M.π.comp V.subtype) = T' := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      exact (g u).2
    · intro t ht
      have htop : (⟨t, ht⟩ : T') ∈ (⊤ : Subgroup T') := Subgroup.mem_top _
      rw [← hpc_map] at htop
      obtain ⟨u, hu, hgu⟩ := Subgroup.mem_map.1 htop
      exact Subgroup.mem_map.2 ⟨u, hu, congrArg Subtype.val hgu⟩
  let K' : Subgroup ↥S := (pCore 2 V).map V.subtype
  let U : Subgroup Ω := K'.map S.subtype
  have hK'2 : IsPGroup 2 K' := (CFSG.pCore_isPGroup (p := 2) (G := V)).map V.subtype
  have hU2 : IsPGroup 2 U := hK'2.map S.subtype
  have hUsub : U.subgroupOf S = K' := Subgroup.subgroupOf_map_subtype_eq_self K'
  have hUpi : piImg M U = T' := by
    unfold piImg
    rw [hUsub]
    dsimp [K']
    rw [Subgroup.map_map]
    exact hpc_T
  have hUX : U ≤ X := by
    calc U = K'.map S.subtype := rfl
      _ ≤ XS.map S.subtype := Subgroup.map_mono ((Subgroup.map_subtype_le _).trans inf_le_left)
      _ = X := Subgroup.map_subgroupOf_eq_of_le hXS
  have hU1 : U ≠ ⊥ := by
    intro h
    apply hT'1
    have hbot : piImg M U = ⊥ := by
      rw [h]
      simp [piImg]
    rwa [hUpi] at hbot
  refine ⟨U, hUX, hU1, hU2, hUpi, ?_⟩
  intro s hsX hsNT
  have hpnXS : s ∈ Subgroup.normalizer (XS : Set ↥S) :=
    (mem_normalizer_subgroupOf_iff hXS s).2 hsX
  have hpnTS : s ∈ Subgroup.normalizer (TS : Set ↥S) :=
    Subgroup.le_normalizer_comap M.π (Subgroup.mem_comap.2 hsNT)
  have hpnV : s ∈ Subgroup.normalizer (V : Set ↥S) :=
    Subgroup.inf_normalizer_le_normalizer_inf (H := XS) (K := TS) ⟨hpnXS, hpnTS⟩
  have hchar : Subgroup.normalizer (V : Set ↥S) ≤ Subgroup.normalizer (K' : Set ↥S) := by
    have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := V) (K := pCore 2 V)
    simpa [K'] using this
  exact Subgroup.le_normalizer_map S.subtype (Subgroup.mem_map_of_mem S.subtype (hchar hpnV))

private theorem exists_twoLocal_lift_aux1 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    {G₀ : Type} [Group G₀] {N D K : Subgroup Ω} {x : Ω} (hcfg : Cfg173 p S B N D K x)
    (M : S172X.S172Model S B G₀) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) {E : Subgroup G₀}
    (hE : IsElemAbelian p E) :
    ∃ P E' : Subgroup Ω, P ≤ S ∧ IsElemAbelian p P ∧ piImg M P = E ∧
      Nat.card P = Nat.card E ∧ IsElemAbelian p E' ∧ Nat.card E' = p * Nat.card E ∧
      E' = Subgroup.zpowers x ⊔ P := by
  have hp := hcfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hPS, hP_el, hPpi, hPcard, -⟩ := exists_pLift hcfg M hZ hE
  have hxp : x ^ p = 1 := hcfg.elem.2 x hcfg.mem
  have hxord : orderOf x = p := orderOf_eq_prime hxp hcfg.ne_one
  have hxc : x ∈ Subgroup.centralizer (S : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  have hxp_p : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxord, pow_one])
  have hinf : Subgroup.zpowers x ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyz, hyP⟩ := Subgroup.mem_inf.1 hy
    have hyS : y ∈ S := hPS hyP
    have hycent : y ∈ Subgroup.centralizer (S : Set Ω) := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyz
      exact Subgroup.zpow_mem _ hxc n
    have hycenter : (⟨y, hyS⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro t
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hycent (t : Ω) t.2)
    have hymap : y ∈ (Subgroup.center ↥S).map S.subtype := ⟨⟨y, hyS⟩, hycenter, rfl⟩
    have hdis : Disjoint (Subgroup.zpowers x) ((Subgroup.center ↥S).map S.subtype) :=
      (TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup
        (C := (Subgroup.center ↥S).map S.subtype) (Q := Subgroup.zpowers x)
        (not_dvd_card_center_map hZ) hxp_p).symm
    exact Subgroup.disjoint_def.1 hdis hyz hymap
  have hxel : IsElemAbelian p (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hxp
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hxb : x * b = b * x := (Subgroup.mem_centralizer_iff.1 hxc b (hPS hb)).symm
    exact (Commute.zpow_left hxb n).eq
  have hE'el : IsElemAbelian p (Subgroup.zpowers x ⊔ P) :=
    IsElemAbelian.sup_of_commute hxel hP_el hcomm
  have hE'card : Nat.card ↥(Subgroup.zpowers x ⊔ P) = p * Nat.card E := by
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.zpowers x) P hcomm).1
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hxord, hPcard] at hcard
    exact hcard
  exact ⟨P, Subgroup.zpowers x ⊔ P, hPS, hP_el, hPpi, hPcard, hE'el, hE'card, rfl⟩

theorem exists_twoLocal_lift
 (hcfg : Cfg173 p S B N D K x) (M : S172X.S172Model S B G₀)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) {E T' : Subgroup G₀} (hE : IsElemAbelian p E) (hT'1 : T' ≠ ⊥)
    (hT'2 : IsPGroup 2 T') (hET : E ≤ Subgroup.normalizer (T' : Set G₀)) :
    ∃ E' U : Subgroup Ω, IsElemAbelian p E' ∧ Nat.card E' = p * Nat.card E ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E' ≤ Subgroup.normalizer (U : Set Ω) := by
  obtain ⟨P, E', hPS, hP_el, hPpi, hPcard, hE'el, hE'card, hE'def⟩ :=
    exists_twoLocal_lift_aux1 hcfg M hZ hE
  have hxc : x ∈ Subgroup.centralizer (S : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  have hT'le : T' ≤ piImg M S := by
    rw [piImg, Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective M.π M.surj]
    exact le_top
  obtain ⟨U, hUS, hU1, hU2, hUpi, hUnorm⟩ :=
    exists_twoCore_preimage_lift M (X := S) le_rfl hT'le hT'2 hT'1
  have hP_norm : P ≤ Subgroup.normalizer (U : Set Ω) := by
    intro p hpP
    refine hUnorm ⟨p, hPS hpP⟩ (Subgroup.le_normalizer (hPS hpP)) ?_
    have hpE : M.π (⟨p, hPS hpP⟩ : ↥S) ∈ piImg M P :=
      Subgroup.mem_map_of_mem M.π (Subgroup.mem_subgroupOf.2 hpP)
    rw [hPpi] at hpE
    exact hET hpE
  have hzp_norm : Subgroup.zpowers x ≤ Subgroup.normalizer (U : Set Ω) := by
    have hzpc : Subgroup.zpowers x ≤ Subgroup.centralizer (S : Set Ω) := Subgroup.zpowers_le.2 hxc
    exact hzpc.trans ((Subgroup.centralizer_le hUS).trans (Subgroup.centralizer_le_normalizer (U : Set Ω)))
  refine ⟨E', U, hE'el, hE'card, hU1, hU2, ?_⟩
  rw [hE'def]
  exact sup_le hzp_norm hP_norm

theorem pow_rank_le_card_range [Finite G₀] (hcfg : Cfg173 p S B N D K x) (M : S172X.S172Model S B G₀)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) : p ^ GLATwoLocalRank p G₀ ≤ Nat.card M.β.range := by
  have hp := hcfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨T₀, hT₀1, hT₀2, -⟩ := exists_two_subgroup_of_hb hcfg M
  obtain ⟨T', hT'1, hT'2, E, hET, hE, hEcard⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Proving.exists_twoLocal_attaining_GLATwoLocalRank hp
      ⟨T₀, hT₀1, hT₀2⟩
  obtain ⟨E', U, hE'el, hE'card, hU1, hU2, hE'U⟩ :=
    exists_twoLocal_lift hcfg M hZ hE hT'1 hT'2 hET
  have hbound := card_le_pow_glaTwoLocalRank hp hE'el hU1 hU2 hE'U
  rw [hE'card, hEcard] at hbound
  have h3 : p * p ^ GLATwoLocalRank p G₀ ≤ p * Nat.card M.β.range := by
    calc p * p ^ GLATwoLocalRank p G₀ ≤ p ^ GLATwoLocalRank p Ω := hbound
      _ = Nat.card B := hcfg.bmax.2.1.symm
      _ = p * Nat.card M.β.range := card_eq_mul_card_range hcfg M
  exact Nat.le_of_mul_le_mul_left h3 hp.pos

theorem isBmax_range [Finite G₀] (hcfg : Cfg173 p S B N D K x) (M : S172X.S172Model S B G₀)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) : GLAIsBmax p M.β.range := by
  refine ⟨M.isElemAbelian_range_β hcfg.elem,
    le_antisymm (card_range_le hcfg M) (pow_rank_le_card_range hcfg M hZ), ?_⟩
  obtain ⟨T', hT'1, hT'2, hT'N⟩ := exists_two_subgroup_of_hb hcfg M
  exact ⟨T', hT'1, hT'2, hT'N⟩

private theorem piImg_normalizer_eq_aux1 {Ω : Type} [Group Ω] {S B : Subgroup Ω}
    {G₀ : Type} [Group G₀] (M : S172X.S172Model S B G₀) {b : Ω} (hbB : b ∈ B) (hbS : b ∈ S) :
    M.β ⟨b, hbB⟩ = M.π ⟨b, hbS⟩ := by
  obtain ⟨s0, c, hc, hbc, hβ⟩ := M.split ⟨b, hbB⟩
  have hcS : c ∈ S := by
    have hb_eq : b = (s0 : Ω) * c := by simpa using hbc
    have hce : c = (s0 : Ω)⁻¹ * b := by rw [hb_eq]; group
    rw [hce]
    exact S.mul_mem (S.inv_mem s0.2) hbS
  have hc_center : (⟨c, hcS⟩ : ↥S) ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro t
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hc (t : Ω) t.2)
  have hπc : M.π ⟨c, hcS⟩ = 1 := by
    rw [← M.ker_π] at hc_center
    simpa using hc_center
  have hs_eq : (⟨b, hbS⟩ : ↥S) = s0 * ⟨c, hcS⟩ := Subtype.ext hbc
  calc M.β ⟨b, hbB⟩ = M.π s0 := hβ
    _ = M.π ⟨b, hbS⟩ := by rw [hs_eq, map_mul, hπc, mul_one]

private theorem piImg_normalizer_eq_aux2 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    {G₀ : Type} [Group G₀] {N D K : Subgroup Ω} {x : Ω} (hcfg : Cfg173 p S B N D K x)
    (M : S172X.S172Model S B G₀) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) :
    M.β.range = piImg M (B ⊓ S) := by
  have hB : B = Subgroup.zpowers x ⊔ B ⊓ S := eq_zpowers_sup_inf hcfg M hZ
  have hxc : x ∈ Subgroup.centralizer (S : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  have hβx : M.β ⟨x, hcfg.mem⟩ = 1 :=
    (M.β_eq_one_iff_mem_zpowers hcfg.cent ⟨x, hcfg.mem⟩).2 (Subgroup.mem_zpowers x)
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ B ⊓ S, Commute a b := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hxb : Commute x b := by
      show x * b = b * x
      exact (Subgroup.mem_centralizer_iff.1 hxc b hb.2).symm
    exact (Commute.zpow_left hxb n)
  apply le_antisymm
  · rintro g ⟨b, rfl⟩
    have hb : (b : Ω) ∈ Subgroup.zpowers x ⊔ B ⊓ S := by rw [← hB]; exact b.2
    obtain ⟨z, hz, s, hs, hzs⟩ := (CFSG.mem_sup_of_commute hcomm).1 hb
    have hzB : z ∈ B := (Subgroup.zpowers_le.2 hcfg.mem) hz
    have hβz : M.β ⟨z, hzB⟩ = 1 := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      rw [show (⟨x ^ n, _⟩ : ↥B) = (⟨x, hcfg.mem⟩ : ↥B) ^ n from rfl,
        map_zpow, hβx, one_zpow]
    refine Subgroup.mem_map.2 ⟨⟨s, hs.2⟩, hs, ?_⟩
    have hbs : (⟨z * s, B.mul_mem hzB hs.1⟩ : ↥B) = b := Subtype.ext hzs
    calc M.π (⟨s, hs.2⟩ : ↥S) = M.β ⟨s, hs.1⟩ :=
        (piImg_normalizer_eq_aux1 M hs.1 hs.2).symm
      _ = M.β b := by
        rw [← hbs]
        rw [show (⟨z * s, B.mul_mem hzB hs.1⟩ : ↥B)
            = ⟨z, hzB⟩ * ⟨s, hs.1⟩ from rfl, map_mul, hβz, one_mul]
  · rintro g hg
    obtain ⟨s, hs, hπs⟩ := Subgroup.mem_map.1 hg
    have hsBS : (s : Ω) ∈ B ⊓ S := hs
    refine ⟨⟨s, hsBS.1⟩, ?_⟩
    rw [← hπs]
    exact piImg_normalizer_eq_aux1 M hsBS.1 s.2

private theorem piImg_normalizer_eq_aux3 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    {G₀ : Type} [Group G₀] {N D K : Subgroup Ω} {x : Ω} (hcfg : Cfg173 p S B N D K x)
    (M : S172X.S172Model S B G₀) {P : Subgroup Ω} (hPS : P ≤ S) (hP_el : IsElemAbelian p P)
    (hPpi : piImg M P = M.β.range)
    (hPmax : ∀ Q : Subgroup Ω, Q ≤ S → IsPGroup p Q → piImg M Q ≤ M.β.range → Q ≤ P)
    {s : ↥S} (hyN : M.π s ∈ Subgroup.normalizer (M.β.range : Set G₀)) :
    (s : Ω) ∈ Subgroup.normalizer (P : Set Ω) := by
  haveI : Fact p.Prime := ⟨hcfg.prime⟩
  let Pconj : Subgroup Ω := P.map (MulAut.conj (s : Ω))
  have hPconjS : Pconj ≤ S := by
    rintro _ ⟨p, hp, rfl⟩
    exact S.mul_mem (S.mul_mem s.2 (hPS hp)) (S.inv_mem s.2)
  have hPconjp : IsPGroup p Pconj := (isPGroup_of_isElemAbelian hP_el).map _
  have hPconjE : piImg M Pconj ≤ M.β.range := by
    intro z hz
    obtain ⟨u, huS, huz⟩ := Subgroup.mem_map.1 hz
    obtain ⟨p, hpP, hpu⟩ := Subgroup.mem_map.1 (huS : (u : Ω) ∈ Pconj)
    have hpS : p ∈ S := hPS hpP
    have hpE : M.π ⟨p, hpS⟩ ∈ M.β.range := by
      rw [← hPpi]
      exact Subgroup.mem_map_of_mem M.π (show (⟨p, hpS⟩ : ↥S) ∈ P.subgroupOf S from hpP)
    have hyconj : M.π s * M.π ⟨p, hpS⟩ * (M.π s)⁻¹ ∈ M.β.range :=
      (Subgroup.mem_normalizer_iff.1 hyN (M.π ⟨p, hpS⟩)).1 hpE
    have hconjS : (s : Ω) * p * (s : Ω)⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem s.2 hpS) (S.inv_mem s.2)
    have hu_eq : u = ⟨(s : Ω) * p * (s : Ω)⁻¹, hconjS⟩ := by
      apply Subtype.ext
      simpa [MulAut.conj_apply] using hpu.symm
    rw [← huz, hu_eq]
    have hval : M.π (⟨(s : Ω) * p * (s : Ω)⁻¹, hconjS⟩ : ↥S) =
        M.π s * M.π ⟨p, hpS⟩ * (M.π s)⁻¹ := by
      rw [show (⟨(s : Ω) * p * (s : Ω)⁻¹, hconjS⟩ : ↥S)
          = s * ⟨p, hpS⟩ * s⁻¹ from rfl, map_mul, map_mul, map_inv]
    rw [hval]
    exact hyconj
  have hle : Pconj ≤ P := hPmax Pconj hPconjS hPconjp hPconjE
  have hcard : Nat.card Pconj = Nat.card P := by
    dsimp [Pconj]
    rw [Subgroup.card_map_of_injective (MulAut.conj (s : Ω)).injective]
  have hEq : Pconj = P := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  simpa [Pconj] using hEq

private theorem piImg_normalizer_eq_aux4 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    {G₀ : Type} [Group G₀] {N D K : Subgroup Ω} {x : Ω} (hcfg : Cfg173 p S B N D K x)
    (M : S172X.S172Model S B G₀) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S))
    (hB : B = Subgroup.zpowers x ⊔ B ⊓ S) (hxp : x ^ p = 1)
    (hxord : orderOf x = p) (hxc : x ∈ Subgroup.centralizer (S : Set Ω)) :
    Nat.card ↥(B ⊓ S) = Nat.card M.β.range := by
  have hp := hcfg.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ B ⊓ S, Commute a b := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hxb : Commute x b := by
      show x * b = b * x
      exact (Subgroup.mem_centralizer_iff.1 hxc b hb.2).symm
    exact (Commute.zpow_left hxb n)
  have hinf : Subgroup.zpowers x ⊓ (B ⊓ S) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyz, hyBS⟩ := Subgroup.mem_inf.1 hy
    have hycent : y ∈ Subgroup.centralizer (S : Set Ω) := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyz
      exact Subgroup.zpow_mem _ hxc n
    have hycenter : (⟨y, hyBS.2⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro t
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hycent (t : Ω) t.2)
    have hymap : y ∈ (Subgroup.center ↥S).map S.subtype := ⟨⟨y, hyBS.2⟩, hycenter, rfl⟩
    have hdis : Disjoint (Subgroup.zpowers x) ((Subgroup.center ↥S).map S.subtype) :=
      (TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup
        (C := (Subgroup.center ↥S).map S.subtype) (Q := Subgroup.zpowers x)
        (not_dvd_card_center_map hZ)
        (isPGroup_of_isElemAbelian (CFSG.Open.isElemAbelian_zpowers hxp))).symm
    exact Subgroup.disjoint_def.1 hdis hyz hymap
  have hcard1 : Nat.card B = p * Nat.card ↥(B ⊓ S) := by
    have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.zpowers x) (B ⊓ S) hcomm).1
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hxord, ← hB] at hcard
    exact hcard
  have hcard2 : Nat.card B = p * Nat.card M.β.range := card_eq_mul_card_range hcfg M
  exact Nat.eq_of_mul_eq_mul_left hp.pos (hcard1.symm.trans hcard2)

private theorem piImg_normalizer_eq_aux5 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    {G₀ : Type} [Group G₀] {N D K : Subgroup Ω} {x : Ω} (hcfg : Cfg173 p S B N D K x)
    (M : S172X.S172Model S B G₀) (hβpi : M.β.range = piImg M (B ⊓ S)) {P : Subgroup Ω}
    (hPcard : Nat.card P = Nat.card M.β.range)
    (hPmax : ∀ Q : Subgroup Ω, Q ≤ S → IsPGroup p Q → piImg M Q ≤ M.β.range → Q ≤ P)
    (hcardBS : Nat.card ↥(B ⊓ S) = Nat.card M.β.range) : B ⊓ S = P := by
  have hp := hcfg.prime
  have hle : B ⊓ S ≤ P := by
    refine hPmax (B ⊓ S) inf_le_right
      (isPGroup_of_isElemAbelian (isElemAbelian_mono hcfg.elem inf_le_left)) ?_
    rw [← hβpi]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hPcard, hcardBS])

private theorem piImg_normalizer_eq_aux6 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    {G₀ : Type} [Group G₀] {N D K : Subgroup Ω} {x : Ω} (hcfg : Cfg173 p S B N D K x)
    (M : S172X.S172Model S B G₀) {P : Subgroup Ω} (hPS : P ≤ S)
    (hPpi : piImg M P = M.β.range) (hBinfP : B ⊓ S = P) :
    piImg M (Subgroup.normalizer (B : Set Ω)) ≤ Subgroup.normalizer (M.β.range : Set G₀) := by
  rintro y ⟨s, hsN, hπs⟩
  rw [← hπs]
  have hsN' : (s : Ω) ∈ Subgroup.normalizer (B : Set Ω) := hsN
  have hsP : (s : Ω) ∈ Subgroup.normalizer (P : Set Ω) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      have htBS : t ∈ B ⊓ S := by rw [hBinfP]; exact ht
      have hconjB : (s : Ω) * t * (s : Ω)⁻¹ ∈ B :=
        (Subgroup.mem_normalizer_iff.1 hsN' t).1 htBS.1
      have hconjS : (s : Ω) * t * (s : Ω)⁻¹ ∈ S :=
        S.mul_mem (S.mul_mem s.2 htBS.2) (S.inv_mem s.2)
      rw [← hBinfP]
      exact ⟨hconjB, hconjS⟩
    · intro ht
      have htP : (s : Ω) * t * (s : Ω)⁻¹ ∈ P := ht
      have hconjS : (s : Ω) * t * (s : Ω)⁻¹ ∈ S := hPS htP
      have htS : t ∈ S := by
        have e : t = (s : Ω)⁻¹ * ((s : Ω) * t * (s : Ω)⁻¹) * (s : Ω) := by group
        rw [e]
        exact S.mul_mem (S.mul_mem (S.inv_mem s.2) hconjS) s.2
      have hconjB : (s : Ω) * t * (s : Ω)⁻¹ ∈ B := by
        have hconjBS : (s : Ω) * t * (s : Ω)⁻¹ ∈ B ⊓ S := by
          rw [hBinfP]
          exact htP
        exact hconjBS.1
      have htB : t ∈ B := (Subgroup.mem_normalizer_iff.1 hsN' t).2 hconjB
      rw [← hBinfP]
      exact ⟨htB, htS⟩
  have hsPN : s ∈ Subgroup.normalizer ((P.subgroupOf S : Subgroup ↥S) : Set ↥S) :=
    (mem_normalizer_subgroupOf_iff hPS s).2 hsP
  have hNmap := Subgroup.le_normalizer_map (H := P.subgroupOf S) M.π
    (Subgroup.mem_map_of_mem M.π hsPN)
  have hset : ((P.subgroupOf S : Subgroup ↥S).map M.π : Set G₀) = (M.β.range : Set G₀) :=
    congrArg (fun H : Subgroup G₀ => (H : Set G₀)) hPpi
  rwa [hset] at hNmap

private theorem piImg_normalizer_eq_aux7 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    {G₀ : Type} [Group G₀] {N D K : Subgroup Ω} {x : Ω} (hcfg : Cfg173 p S B N D K x)
    (M : S172X.S172Model S B G₀) {P : Subgroup Ω} (hPS : P ≤ S) (hP_el : IsElemAbelian p P)
    (hPpi : piImg M P = M.β.range)
    (hPmax : ∀ Q : Subgroup Ω, Q ≤ S → IsPGroup p Q → piImg M Q ≤ M.β.range → Q ≤ P)
    (hB : B = Subgroup.zpowers x ⊔ B ⊓ S) (hBinfP : B ⊓ S = P)
    (hxc : x ∈ Subgroup.centralizer (S : Set Ω)) :
    Subgroup.normalizer (M.β.range : Set G₀) ≤ piImg M (Subgroup.normalizer (B : Set Ω)) := by
  intro y hy
  obtain ⟨s, hsπ⟩ := M.surj y
  rw [← hsπ] at hy ⊢
  have hsP : (s : Ω) ∈ Subgroup.normalizer (P : Set Ω) :=
    piImg_normalizer_eq_aux3 hcfg M hPS hP_el hPpi hPmax hy
  have hmapP : P.map (MulAut.conj (s : Ω)) = P :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hsP
  have hmapZ : (Subgroup.zpowers x).map (MulAut.conj (s : Ω)) = Subgroup.zpowers x := by
    rw [MonoidHom.map_zpowers]
    have hcommxs : x * (s : Ω) = (s : Ω) * x :=
      (Subgroup.mem_centralizer_iff.1 hxc (s : Ω) s.2).symm
    have hconj_x : MulAut.conj (s : Ω) x = x := by
      show (s : Ω) * x * (s : Ω)⁻¹ = x
      rw [← hcommxs]
      group
    change Subgroup.zpowers ((MulAut.conj (s : Ω)) x) = Subgroup.zpowers x
    rw [hconj_x]
  have hBP : B = Subgroup.zpowers x ⊔ P := by rw [hB, hBinfP]
  have hmapB : B.map (MulAut.conj (s : Ω)) = B := by
    calc B.map (MulAut.conj (s : Ω))
        = (Subgroup.zpowers x ⊔ P).map (MulAut.conj (s : Ω)) := by rw [hBP]
      _ = Subgroup.zpowers x ⊔ P := by rw [Subgroup.map_sup, hmapZ, hmapP]
      _ = B := hBP.symm
  have hsN : (s : Ω) ∈ Subgroup.normalizer (B : Set Ω) :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).2 hmapB
  exact ⟨s, hsN, rfl⟩

theorem piImg_normalizer_eq (hcfg : Cfg173 p S B N D K x) (M : S172X.S172Model S B G₀)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) :
    piImg M (Subgroup.normalizer (B : Set Ω)) = Subgroup.normalizer (M.β.range : Set G₀) := by
  haveI : Fact p.Prime := ⟨hcfg.prime⟩
  have hβpi := piImg_normalizer_eq_aux2 hcfg M hZ
  obtain ⟨P, hPS, hP_el, hPpi, hPcard, hPmax⟩ :=
    exists_pLift hcfg M hZ (M.isElemAbelian_range_β hcfg.elem)
  have hB : B = Subgroup.zpowers x ⊔ B ⊓ S := eq_zpowers_sup_inf hcfg M hZ
  have hxc : x ∈ Subgroup.centralizer (S : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  have hxp : x ^ p = 1 := hcfg.elem.2 x hcfg.mem
  have hxord : orderOf x = p := orderOf_eq_prime hxp hcfg.ne_one
  have hcardBS := piImg_normalizer_eq_aux4 hcfg M hZ hB hxp hxord hxc
  have hBinfP := piImg_normalizer_eq_aux5 hcfg M hβpi hPcard hPmax hcardBS
  exact le_antisymm
    (piImg_normalizer_eq_aux6 hcfg M hPS hPpi hBinfP)
    (piImg_normalizer_eq_aux7 hcfg M hPS hP_el hPpi hPmax hB hBinfP hxc)

end CFSG.LocalAnalysis.GLTheoremA.T173X

end
