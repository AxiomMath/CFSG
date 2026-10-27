module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResProd
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerD3Basic

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup
open scoped commutatorElement

section FConstruction

variable {N Y : Type} [Group N] [Group Y]

structure FSetup (V : Subgroup N) (q : N →* Y) (ρ : Y →* MulAut V) (S1 S2 : Subgroup Y)
    (D1 D2 : Subgroup V) (z : N) : Prop where
  hq : Function.Surjective q
  hker : q.ker = V
  hρ : ∀ (n : N) (v : V), ((ρ (q n) v : V) : N) = n * v * n⁻¹
  hVc : ∀ a b : V, a * b = b * a
  e1 : Nonempty (S1 ≃* alternatingGroup (Fin 8))
  e2 : Nonempty (S2 ≃* alternatingGroup (Fin 8))
  hcomm : ∀ a ∈ S1, ∀ b ∈ S2, a * b = b * a
  hdisj : Disjoint S1 S2
  hz : z * z = 1
  hz12 : ∀ g ∈ S1, q z * g * (q z)⁻¹ ∈ S2
  hz21 : ∀ g ∈ S2, q z * g * (q z)⁻¹ ∈ S1
  hD1card : Nat.card D1 = 16
  hD2card : Nat.card D2 = 16
  hDinf : D1 ⊓ D2 = ⊥
  hDsup : D1 ⊔ D2 = ⊤
  hfix2 : ∀ g ∈ S2, ∀ u ∈ D1, ρ g u = u
  hfix1 : ∀ g ∈ S1, ∀ u ∈ D2, ρ g u = u
  hinv1 : ∀ g ∈ S1, ∀ u ∈ D1, ρ g u ∈ D1
  hinv2 : ∀ g ∈ S2, ∀ u ∈ D2, ρ g u ∈ D2
  hzD12 : ∀ u ∈ D1, ρ (q z) u ∈ D2
  hzD21 : ∀ u ∈ D2, ρ (q z) u ∈ D1
  hclos : Subgroup.closure {x : V | ∃ g ∈ S1, ∃ u ∈ D1, x = ρ g u * u⁻¹} = D1
  hD2triv : ∀ u ∈ D2, (∀ g ∈ S2, ρ g u = u) → u = 1

variable {V : Subgroup N} {q : N →* Y} {ρ : Y →* MulAut V} {S1 S2 : Subgroup Y}
  {D1 D2 : Subgroup V} {z : N}

namespace FSetup

variable (h : FSetup V q ρ S1 S2 D1 D2 z)
include h

theorem q_eq_one {v : N} (hv : v ∈ V) : q v = 1 := by
  have : v ∈ q.ker := by rw [h.hker]; exact hv
  exact this

theorem mem_V_of_q_eq_one {v : N} (hv : q v = 1) : v ∈ V := by
  have : v ∈ q.ker := hv
  rwa [h.hker] at this

theorem V_le_comap (S : Subgroup Y) : V ≤ S.comap q := fun v hv => by
  rw [mem_comap, h.q_eq_one hv]
  exact S.one_mem

theorem conj_apply_V {n : N} {u : V} : n * (u : N) * n⁻¹ = ((ρ (q n) u : V) : N) := (h.hρ n u).symm

theorem conj_D2 {n : N} (hn : n ∈ S1.comap q) {u : V} (hu : u ∈ D2) :
    n * (u : N) * n⁻¹ = u := by
  rw [h.conj_apply_V, h.hfix1 (q n) hn u hu]

theorem conj_mem_S1 {a b : N} (ha : a ∈ S1.comap q) (hb : b ∈ S2.comap q) :
    b * a * b⁻¹ ∈ S1.comap q := by
  rw [mem_comap, map_mul, map_mul, map_inv]
  have := h.hcomm _ ha _ hb
  rw [← this, mul_assoc, mul_inv_cancel, mul_one]
  exact ha

end FSetup

theorem conj_mem_commutator {S : Subgroup N} {g : N} (hg : ∀ x ∈ S, g * x * g⁻¹ ∈ S) {x : N}
    (hx : x ∈ ⁅S, S⁆) : g * x * g⁻¹ ∈ ⁅S, S⁆ := by
  have h1 : (⁅S, S⁆).map (MulAut.conj g).toMonoidHom ≤ ⁅S, S⁆ := by
    rw [map_commutator]
    exact commutator_mono (fun _ ⟨x', hx', hy⟩ => hy ▸ hg x' hx')
      (fun _ ⟨x', hx', hy⟩ => hy ▸ hg x' hx')
  exact h1 ⟨x, hx, rfl⟩

theorem eq_of_card_le_two {K : Subgroup N} [Finite K] (hK : Nat.card K ≤ 2) {x y : N}
    (hx : x ∈ K) (hy : y ∈ K) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have hdvd : orderOf x ∣ Nat.card K := by
    have := Subgroup.orderOf_dvd_natCard K hx
    exact this
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hne : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.1 h)
  have hle : orderOf x ≤ Nat.card K := Nat.le_of_dvd hpos hdvd
  have hpos' : 0 < orderOf x := Nat.pos_of_dvd_of_pos hdvd hpos
  have hord : orderOf x = 2 := by omega
  have hz : zpowers x = K := by
    refine eq_of_le_of_card_ge (zpowers_le.2 hx) ?_
    rw [Nat.card_zpowers, hord]
    omega
  rw [← hz] at hy
  rcases eq_one_or_eq_of_mem_zpowers hord hy with h | h
  · exact absurd h hy1
  · exact h.symm

namespace FSetup

variable (h : FSetup V q ρ S1 S2 D1 D2 z)
include h

theorem S1_perfect : ⁅S1, S1⁆ = S1 := by
  obtain ⟨e⟩ := h.e1
  have : Group.IsPerfect (alternatingGroup (Fin 8)) := ⟨alt8_commutator⟩
  have : Group.IsPerfect S1 :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.isPerfect_iff.1 this

theorem F_map_q : (⁅S1.comap q, S1.comap q⁆).map q = S1 := by
  rw [map_commutator, map_comap_eq_self_of_surjective h.hq, h.S1_perfect]

omit h in
theorem F_le : ⁅S1.comap q, S1.comap q⁆ ≤ S1.comap q := commutator_le_self _

theorem F_conj_S2 {b x : N} (hb : b ∈ S2.comap q) (hx : x ∈ ⁅S1.comap q, S1.comap q⁆) :
    b * x * b⁻¹ ∈ ⁅S1.comap q, S1.comap q⁆ :=
  conj_mem_commutator (fun _ hy => h.conj_mem_S1 hy hb) hx

theorem D1_le_F : D1.map V.subtype ≤ ⁅S1.comap q, S1.comap q⁆ := by
  rw [Subgroup.map_le_iff_le_comap, ← h.hclos, Subgroup.closure_le]
  rintro x ⟨g, hg, u, hu, rfl⟩
  obtain ⟨n, rfl⟩ := h.hq g
  have hn : n ∈ S1.comap q := hg
  have hu' : (u : N) ∈ S1.comap q := h.V_le_comap S1 u.2
  have e1 : ((ρ (q n) u * u⁻¹ : V) : N) = ⁅n, (u : N)⁆ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, h.hρ n u]
    rfl
  show ((ρ (q n) u * u⁻¹ : V) : N) ∈ ⁅S1.comap q, S1.comap q⁆
  rw [e1]
  exact commutator_mem_commutator hn hu'

theorem exists_mul_V (v : V) : ∃ d1 ∈ D1, ∃ d2 ∈ D2, d1 * d2 = v := by
  have hN : D2.Normal := ⟨fun n hn g => by
    rw [h.hVc g n, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩
  exact Subgroup.mem_sup_of_normal_right.1 (h.hDsup ▸ mem_top v)

theorem S1_eq_mul {a : N} (ha : a ∈ S1.comap q) :
    ∃ f ∈ ⁅S1.comap q, S1.comap q⁆, ∃ d ∈ D2.map V.subtype, a = f * d := by
  have hqa : q a ∈ (⁅S1.comap q, S1.comap q⁆).map q := by rw [h.F_map_q]; exact ha
  obtain ⟨f, hf, hfa⟩ := hqa
  have hv : f⁻¹ * a ∈ V := by
    apply h.mem_V_of_q_eq_one
    rw [map_mul, map_inv, hfa]
    group
  obtain ⟨d1, hd1, d2, hd2, hd12⟩ := h.exists_mul_V ⟨f⁻¹ * a, hv⟩
  refine ⟨f * d1, mul_mem hf (h.D1_le_F ⟨d1, hd1, rfl⟩), d2, ⟨d2, hd2, rfl⟩, ?_⟩
  have := congrArg Subtype.val hd12
  simp only [Subgroup.coe_mul] at this
  calc a = f * (f⁻¹ * a) := by group
    _ = f * ((d1 : N) * d2) := by rw [← this]
    _ = f * d1 * d2 := by group

end FSetup

theorem commutator_mul_of_commute {S : Subgroup N} {y y' k k' : N} (hy : y ∈ S) (hy' : y' ∈ S)
    (hk' : k' ∈ S) (hkc : ∀ g ∈ S, k * g = g * k) (hkc' : ∀ g ∈ S, k' * g = g * k') :
    ⁅y * k, y' * k'⁆ = ⁅y, y'⁆ := by
  have h1 : Commute k (y' * k') := hkc _ (mul_mem hy' hk')
  have h2 : Commute y k' := (hkc' y hy).symm
  rw [commutatorElement_mul_left_eq_conj_mul, h1.commutator_eq, mul_one, mul_inv_cancel, one_mul,
    commutatorElement_mul_right_eq_mul_conj, h2.commutator_eq, mul_one, mul_inv_cancel_right]

namespace FSetup

variable (h : FSetup V q ρ S1 S2 D1 D2 z)
include h

theorem F_perfect : ⁅⁅S1.comap q, S1.comap q⁆, ⁅S1.comap q, S1.comap q⁆⁆ =
    ⁅S1.comap q, S1.comap q⁆ := by
  refine le_antisymm (commutator_le_self _) ?_
  rw [commutator_le]
  intro a ha b hb
  obtain ⟨f, hf, d, hd, rfl⟩ := h.S1_eq_mul ha
  obtain ⟨f', hf', d', hd', rfl⟩ := h.S1_eq_mul hb
  have hdV : ∀ x ∈ D2.map V.subtype, x ∈ S1.comap q := by
    rintro _ ⟨u, hu, rfl⟩
    exact h.V_le_comap S1 u.2
  have hcen : ∀ x ∈ D2.map V.subtype, ∀ g ∈ S1.comap q, x * g = g * x := by
    rintro _ ⟨u, hu, rfl⟩ g hg
    have h1 := h.conj_D2 hg hu
    have h2 : g * (u : N) = (u : N) * g := by
      calc g * (u : N) = (g * u * g⁻¹) * g := by group
        _ = u * g := by rw [h1]
    exact h2.symm
  rw [commutator_mul_of_commute (F_le hf) (F_le hf') (hdV d' hd') (hcen d hd)
    (hcen d' hd')]
  exact commutator_mem_commutator hf hf'

theorem inv_conj_mem_D1 {f g : N} (hf : f ∈ V) (hg : g ∈ S1.comap q) :
    f⁻¹ * (g * f * g⁻¹) ∈ D1.map V.subtype := by
  let _ : CommGroup V := { (inferInstance : Group V) with mul_comm := h.hVc }
  obtain ⟨d1, hd1, d2, hd2, hd12⟩ := h.exists_mul_V ⟨f, hf⟩
  have hf' : f = ((d1 * d2 : V) : N) := (congrArg Subtype.val hd12).symm
  have e1 : g * f * g⁻¹ = ((ρ (q g) (d1 * d2) : V) : N) := by
    rw [h.hρ g (d1 * d2), ← hf']
  have e2 : ρ (q g) (d1 * d2) = ρ (q g) d1 * d2 := by
    rw [map_mul, h.hfix1 (q g) hg d2 hd2]
  have key : d1⁻¹ * ρ (q g) d1 = (d1 * d2)⁻¹ * ρ (q g) (d1 * d2) := by
    rw [e2, mul_inv_rev]
    calc d1⁻¹ * ρ (q g) d1 = d1⁻¹ * ρ (q g) d1 * (d2⁻¹ * d2) := by rw [inv_mul_cancel, mul_one]
      _ = d2⁻¹ * d1⁻¹ * (ρ (q g) d1 * d2) := by ac_rfl
  refine ⟨d1⁻¹ * ρ (q g) d1, mul_mem (inv_mem hd1) (h.hinv1 (q g) hg d1 hd1), ?_⟩
  rw [e1, hf']
  exact congrArg Subtype.val key

variable [Finite N] in
theorem F_inf_D2 {c : N} (hcF : c ∈ ⁅S1.comap q, S1.comap q⁆) (hc2 : c ∈ D2.map V.subtype) :
    c = 1 := by
  obtain ⟨e⟩ := h.e1
  set F := ⁅S1.comap q, S1.comap q⁆ with hF
  have hFS : F ≤ S1.comap q := F_le
  have hDt1 : D1.map V.subtype ≤ F := h.D1_le_F
  have hDtV : ∀ x ∈ D1.map V.subtype, x ∈ V := by
    rintro _ ⟨u, hu, rfl⟩
    exact u.2
  have hnorm : ((D1.map V.subtype).subgroupOf F).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨u, hu, hux⟩ := hx
    have hg : (g : N) ∈ S1.comap q := hFS g.2
    rw [mem_subgroupOf]
    refine ⟨ρ (q g) u, h.hinv1 (q g) hg u hu, ?_⟩
    have hux' : (u : N) = (x : N) := hux
    rw [Subgroup.coe_subtype, h.hρ g u, hux']
    rfl
  let φ0 : F →* S1 := (q.comp F.subtype).codRestrict S1 (fun x => hFS x.2)
  let φ : F →* alternatingGroup (Fin 8) := e.toMonoidHom.comp φ0
  have hφval : ∀ x : F, φ x = e ⟨q x, hFS x.2⟩ := fun x => rfl
  have hφs : Function.Surjective φ := by
    intro a
    have hs : (e.symm a : Y) ∈ (F).map q := by rw [h.F_map_q]; exact (e.symm a).2
    obtain ⟨x, hx, hxa⟩ := hs
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [hφval]
    have : (⟨q x, hFS hx⟩ : S1) = e.symm a := Subtype.ext hxa
    rw [this, MulEquiv.apply_symm_apply]
  have hφker : (D1.map V.subtype).subgroupOf F ≤ φ.ker := by
    intro x hx
    have hxV : (x : N) ∈ V := hDtV _ hx
    rw [MonoidHom.mem_ker, hφval]
    have : (⟨q x, hFS x.2⟩ : S1) = 1 := Subtype.ext (h.q_eq_one hxV)
    rw [this, map_one]
  let φ' := QuotientGroup.lift ((D1.map V.subtype).subgroupOf F) φ hφker
  have hφ's : Function.Surjective φ' := by
    intro a
    obtain ⟨x, hx⟩ := hφs a
    exact ⟨QuotientGroup.mk x, by rw [QuotientGroup.lift_mk]; exact hx⟩
  have hperf : commutator (F ⧸ (D1.map V.subtype).subgroupOf F) = ⊤ := by
    have : Group.IsPerfect F := Subgroup.isPerfect_iff.2 h.F_perfect
    exact Group.IsPerfect.commutator_eq_top
  have hcentral : φ'.ker ≤ center (F ⧸ (D1.map V.subtype).subgroupOf F) := by
    intro y hy
    obtain ⟨f, rfl⟩ := QuotientGroup.mk_surjective y
    have hf1 : q f = 1 := by
      have h1 : φ' (QuotientGroup.mk f) = 1 := hy
      rw [QuotientGroup.lift_mk, hφval] at h1
      have h2 : (⟨q f, hFS f.2⟩ : S1) = 1 := e.injective (h1.trans (map_one e).symm)
      exact congrArg Subtype.val h2
    have hfV : (f : N) ∈ V := h.mem_V_of_q_eq_one hf1
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    have hgS : (g : N) ∈ S1.comap q := hFS g.2
    have := h.inv_conj_mem_D1 hfV (inv_mem hgS)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at this ⊢
    have e3 : ((g : N) * f)⁻¹ * (f * g) = (f : N)⁻¹ * ((g : N)⁻¹ * f * g) := by group
    rw [e3]
    exact this
  have hdvd := card_ker_dvd_two_alt8 hperf hφ's hcentral
  have hle2 : Nat.card φ'.ker ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  set T2 : Subgroup N := F ⊓ D2.map V.subtype with hT2
  have hT2le : Nat.card T2 ≤ 2 := by
    let ι : T2 → φ'.ker := fun c => ⟨(QuotientGroup.mk (⟨c.1, c.2.1⟩ : F) :
        F ⧸ (D1.map V.subtype).subgroupOf F), by
      show φ' (QuotientGroup.mk (⟨c.1, c.2.1⟩ : F)) = 1
      rw [QuotientGroup.lift_mk, hφval]
      have hcV : (c : N) ∈ V := by
        obtain ⟨u, hu, hu'⟩ := c.2.2
        rw [← hu']; exact u.2
      have h3 : (⟨q c.1, hFS c.2.1⟩ : S1) = 1 := Subtype.ext (h.q_eq_one hcV)
      rw [h3, map_one]⟩
    have hinj : Function.Injective ι := by
      intro c c' hcc
      have h1 := congrArg Subtype.val hcc
      simp only [ι] at h1
      rw [QuotientGroup.eq, mem_subgroupOf] at h1
      have hmem1 : ((⟨c.1, c.2.1⟩ : F)⁻¹ * ⟨c'.1, c'.2.1⟩ : F).1 ∈ D1.map V.subtype := h1
      have hmem2 : ((⟨c.1, c.2.1⟩ : F)⁻¹ * ⟨c'.1, c'.2.1⟩ : F).1 ∈ D2.map V.subtype :=
        mul_mem (inv_mem c.2.2) c'.2.2
      obtain ⟨u1, hu1, hu1e⟩ := hmem1
      obtain ⟨u2, hu2, hu2e⟩ := hmem2
      have hu12 : u1 = u2 := V.subtype_injective (hu1e.trans hu2e.symm)
      have hbot : u1 ∈ D1 ⊓ D2 := ⟨hu1, hu12 ▸ hu2⟩
      rw [h.hDinf, Subgroup.mem_bot] at hbot
      have : ((⟨c.1, c.2.1⟩ : F)⁻¹ * ⟨c'.1, c'.2.1⟩ : F).1 = 1 := by rw [← hu1e, hbot]; rfl
      have h4 : c.1⁻¹ * c'.1 = 1 := this
      exact Subtype.ext (inv_mul_eq_one.1 h4)
    exact (Nat.card_le_card_of_injective ι hinj).trans hle2
  by_contra hc1
  have hcT : c ∈ T2 := ⟨hcF, hc2⟩
  have hfixc : ∀ b ∈ S2.comap q, b * c * b⁻¹ = c := by
    intro b hb
    have hbT : b * c * b⁻¹ ∈ T2 := by
      refine ⟨h.F_conj_S2 hb hcF, ?_⟩
      obtain ⟨u, hu, rfl⟩ := hc2
      exact ⟨ρ (q b) u, h.hinv2 (q b) hb u hu, by rw [Subgroup.coe_subtype, h.hρ b u]⟩
    have hne : b * c * b⁻¹ ≠ 1 := fun h1 => hc1 (by
      calc c = b⁻¹ * (b * c * b⁻¹) * b := by group
        _ = b⁻¹ * 1 * b := by rw [h1]
        _ = 1 := by group)
    exact eq_of_card_le_two hT2le hbT hcT hne hc1
  obtain ⟨u, hu, hue⟩ := hc2
  have hfixu : ∀ g ∈ S2, ρ g u = u := by
    intro g hg
    obtain ⟨b, rfl⟩ := h.hq g
    apply Subtype.ext
    have hue' : (u : N) = c := hue
    rw [h.hρ b u]
    have := hfixc b hg
    rw [← hue'] at this
    exact this
  have := h.hD2triv u hu hfixu
  apply hc1
  rw [← hue, this]
  rfl

variable [Finite N] in
theorem F_inf_V {x : N} (hxF : x ∈ ⁅S1.comap q, S1.comap q⁆) (hxV : x ∈ V) :
    x ∈ D1.map V.subtype := by
  obtain ⟨d1, hd1, d2, hd2, hd12⟩ := h.exists_mul_V ⟨x, hxV⟩
  have hx : x = (d1 : N) * d2 := by simpa using (congrArg Subtype.val hd12).symm
  have hd1F : (d1 : N) ∈ ⁅S1.comap q, S1.comap q⁆ := h.D1_le_F ⟨d1, hd1, rfl⟩
  have hd2F : (d2 : N) ∈ ⁅S1.comap q, S1.comap q⁆ := by
    have : (d2 : N) = (d1 : N)⁻¹ * x := by rw [hx]; group
    rw [this]
    exact mul_mem (inv_mem hd1F) hxF
  have h1 := h.F_inf_D2 hd2F ⟨d2, hd2, rfl⟩
  rw [hx, h1, mul_one]
  exact ⟨d1, hd1, rfl⟩

variable [Finite N] in
theorem card_F : Nat.card (⁅S1.comap q, S1.comap q⁆ : Subgroup N) = 16 * 20160 := by
  obtain ⟨e⟩ := h.e1
  set F := ⁅S1.comap q, S1.comap q⁆ with hF
  have hFS : F ≤ S1.comap q := F_le
  let φ0 : F →* S1 := (q.comp F.subtype).codRestrict S1 (fun x => hFS x.2)
  have hφ0s : Function.Surjective φ0 := by
    intro a
    have hs : (a : Y) ∈ F.map q := by rw [h.F_map_q]; exact a.2
    obtain ⟨x, hx, hxa⟩ := hs
    exact ⟨⟨x, hx⟩, Subtype.ext hxa⟩
  have hker : φ0.ker = (D1.map V.subtype).subgroupOf F := by
    ext x
    constructor
    · intro hx
      have h1 : q x = 1 := congrArg Subtype.val hx
      exact h.F_inf_V x.2 (h.mem_V_of_q_eq_one h1)
    · intro hx
      obtain ⟨u, hu, hux⟩ := hx
      have h1 : q x = 1 := h.q_eq_one (by rw [← show (u : N) = (x : N) from hux]; exact u.2)
      exact Subtype.ext h1
  have hcard := Subgroup.card_ker_mul_card_range φ0
  have hrange : Nat.card φ0.range = 20160 := by
    rw [MonoidHom.range_eq_top_of_surjective φ0 hφ0s, Subgroup.card_top,
      Nat.card_congr e.toEquiv, card_alt8]
  have hkerc : Nat.card φ0.ker = 16 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.D1_le_F).toEquiv,
      ← Nat.card_congr (Subgroup.equivMapOfInjective D1 V.subtype V.subtype_injective).toEquiv,
      h.hD1card]
  rw [← hcard, hkerc, hrange]

variable [Finite N] in
theorem exists_F : ∃ F : Subgroup N, Nat.card F = 2 ^ 10 * 315 ∧
    (∀ a ∈ F, ∀ b ∈ F, a * (z * b * z⁻¹) = (z * b * z⁻¹) * a) ∧
    ∀ a ∈ F, z * a * z⁻¹ ∈ F → a = 1 := by
  set F := ⁅S1.comap q, S1.comap q⁆ with hF
  have hz1 : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.hz
  have hFS : F ≤ S1.comap q := F_le
  have hzS : ∀ a ∈ S1.comap q, z * a * z⁻¹ ∈ S2.comap q := fun a ha => by
    rw [mem_comap, map_mul, map_mul, map_inv]
    exact h.hz12 _ ha
  have hzV : ∀ u : V, z * (u : N) * z⁻¹ ∈ V := fun u => by
    rw [← h.hρ z u]
    exact (ρ (q z) u).2
  have hconj : ∀ w : N, z * (z * w * z⁻¹) * z⁻¹ = w := fun w => by
    calc z * (z * w * z⁻¹) * z⁻¹ = (z * z) * w * (z * z)⁻¹ := by group
      _ = w := by rw [h.hz]; group
  have hzS' : ∀ a ∈ S1.comap q, z⁻¹ * a * z ∈ S2.comap q := fun a ha => by
    rw [show z⁻¹ * a * z = z * a * z⁻¹ by rw [hz1]]
    exact hzS a ha
  have KF : ∀ x ∈ F, ∀ f ∈ F, x = z * f * z⁻¹ → x = 1 := by
    intro x hx f hf hxf
    have hq1 : q x ∈ S1 := hFS hx
    have hq2 : q x ∈ S2 := by
      have : x ∈ S2.comap q := by rw [hxf]; exact hzS f (hFS hf)
      exact this
    have hq : q x = 1 := by
      have : q x ∈ S1 ⊓ S2 := ⟨hq1, hq2⟩
      rw [disjoint_iff.1 h.hdisj, Subgroup.mem_bot] at this
      exact this
    have hxV : x ∈ V := h.mem_V_of_q_eq_one hq
    obtain ⟨u1, hu1, hu1x⟩ := h.F_inf_V hx hxV
    have hfV : f ∈ V := by
      have := hzV ⟨x, hxV⟩
      have e1 : f = z * x * z⁻¹ := by rw [hxf]; exact (hconj f).symm
      rw [e1]
      exact this
    obtain ⟨u2, hu2, hu2f⟩ := h.F_inf_V hf hfV
    have hx2 : x = ((ρ (q z) u2 : V) : N) := by
      rw [h.hρ z u2, show (u2 : N) = f from hu2f, hxf]
    have hu12 : u1 = ρ (q z) u2 := V.subtype_injective (hu1x.trans hx2)
    have hbot : u1 ∈ D1 ⊓ D2 := ⟨hu1, hu12 ▸ h.hzD12 u2 hu2⟩
    rw [h.hDinf, Subgroup.mem_bot] at hbot
    rw [← hu1x, hbot]
    rfl
  refine ⟨F, by rw [h.card_F]; norm_num, ?_, ?_⟩
  · intro a ha b hb
    set b' := z * b * z⁻¹ with hb'
    have hb'S : b' ∈ S2.comap q := hzS b (hFS hb)
    have hA : b' * a⁻¹ * b'⁻¹ ∈ F := h.F_conj_S2 hb'S (inv_mem ha)
    have ha'S : z⁻¹ * a * z ∈ S2.comap q := hzS' a (hFS ha)
    have hB : (z⁻¹ * a * z) * b * (z⁻¹ * a * z)⁻¹ ∈ F := h.F_conj_S2 ha'S hb
    have hx : a * b' * a⁻¹ * b'⁻¹ = 1 := by
      refine KF _ (by
        have : a * b' * a⁻¹ * b'⁻¹ = a * (b' * a⁻¹ * b'⁻¹) := by group
        rw [this]
        exact mul_mem ha hA) ((z⁻¹ * a * z) * b * (z⁻¹ * a * z)⁻¹ * b⁻¹)
        (mul_mem hB (inv_mem hb)) ?_
      rw [hb']
      group
    calc a * b' = a * b' * a⁻¹ * b'⁻¹ * (b' * a) := by group
      _ = b' * a := by rw [hx, one_mul]
  · intro a ha haz
    have h1 := KF _ haz a ha rfl
    calc a = z⁻¹ * (z * a * z⁻¹) * z := by group
      _ = 1 := by rw [h1]; group

end FSetup

end FConstruction

end CFSG.EvenSporadicStandard.M24Std.DRes
